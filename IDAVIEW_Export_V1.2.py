import idc
import ida_ida
import ida_bytes
import ida_xref
import ida_strlist
import idautils
import ida_funcs
import ida_name
import ida_segment
import zipfile
import os

def export_idaview():
    # Получаем актуальный путь к текущей открытой базе
    idb_path = idc.get_idb_path()
    if not idb_path:
        print("[-] Ошибка: Не удалось получить актуальный путь к базе данных.")
        return

    base = os.path.splitext(idb_path)[0]
    out_zip = base + ".IDAVIEW"
    tmp_lst = base + ".tmp.lst"

    out_dir = os.path.dirname(out_zip)
    if out_dir and not os.path.exists(out_dir):
        os.makedirs(out_dir, exist_ok=True)

    min_ea = ida_ida.inf_get_min_ea()
    max_ea = ida_ida.inf_get_max_ea()

    print(f"[*] Генерируем LST файл во временный {tmp_lst}...")
    try:
        idc.gen_file(idc.OFILE_LST, tmp_lst, min_ea, max_ea, 0)
    except AttributeError:
        idc.gen_file(3, tmp_lst, min_ea, max_ea, 0)

    # Локальные кэши для молниеносной работы
    seg_cache = {}
    def fast_seg_name(ea):
        seg = ida_segment.getseg(ea)
        if not seg: return "seg"
        if seg.start_ea not in seg_cache:
            seg_cache[seg.start_ea] = ida_segment.get_segm_name(seg) or "seg"
        return seg_cache[seg.start_ea]

    name_cache = {}
    def fast_name(ea):
        if ea in name_cache: return name_cache[ea]
        n = ida_name.get_name(ea)
        res = n if n else "unk"
        name_cache[ea] = res
        return res

    func_off_cache = {}
    def get_func_off_str(ea):
        if ea in func_off_cache: return func_off_cache[ea]
        f = ida_funcs.get_func(ea)
        if f:
            fname = ida_name.get_name(f.start_ea)
            if not fname: fname = "sub_%X" % f.start_ea
            diff = ea - f.start_ea
            res = f"{fname}+{diff:X}" if diff else fname
        else:
            n = ida_name.get_name(ea)
            res = n if n else f"unk_{ea:X}"
        func_off_cache[ea] = res
        return res

    print("[*] Собираем строки (Strings)...")
    ida_strlist.build_strlist()
    strings = ["Address\tLength\tType\tString"]
    qty = ida_strlist.get_strlist_qty()
    for i in range(qty):
        si = ida_strlist.string_info_t()
        if ida_strlist.get_strlist_item(si, i):
            s = idc.get_strlit_contents(si.ea, -1, si.type)
            if s:
                try:
                    s_dec = s.decode('utf-8', 'ignore')
                except:
                    s_dec = str(s)
                s_dec = s_dec.replace('\n', '\\n').replace('\r', '\\r')
                t = 'U' if si.type == idc.STRTYPE_C_16 else 'C'
                strings.append(f"{fast_seg_name(si.ea)}:{si.ea:08X}\t{si.length:08X}\t{t}\t{s_dec}")

    print("[*] Собираем функции (Functions)...")
    funcs = ["Address\tLength\tFunction name"]
    for ea in idautils.Functions():
        f = ida_funcs.get_func(ea)
        if f:
            funcs.append(f"{fast_seg_name(ea)}:{ea:08X}\t{f.end_ea - f.start_ea:08X}\t{fast_name(ea)}")

    print("[*] Собираем Xrefs (Граф связей)...")
    xrefs_list = set()
    xb = ida_xref.xrefblk_t()
    
    for head in idautils.Heads(min_ea, max_ea):
        ok = xb.first_from(head, ida_xref.XREF_ALL)
        while ok:
            if xb.iscode:
                if xb.to != head + ida_bytes.get_item_size(head):
                    xrefs_list.add(f"{head:08X}\t{xb.to:08X}\tC\t{get_func_off_str(head)}\t{get_func_off_str(xb.to)}")
            else:
                xrefs_list.add(f"{head:08X}\t{xb.to:08X}\tD\t{get_func_off_str(head)}\t{get_func_off_str(xb.to)}")
            ok = xb.next_from()

    print(f"[*] Упаковываем базу в {out_zip}...")
    with zipfile.ZipFile(out_zip, 'w', zipfile.ZIP_DEFLATED, compresslevel=1) as zf:
        if os.path.exists(tmp_lst):
            zf.write(tmp_lst, arcname="ida.lst")
        zf.writestr("strings.txt", "\n".join(strings))
        zf.writestr("functions.txt", "\n".join(funcs))
        zf.writestr("xrefs.txt", "\n".join(xrefs_list))

    if os.path.exists(tmp_lst):
        os.remove(tmp_lst)
        
    print(f"[+] Успешно! Файл экспортирован в {out_zip}")

if __name__ == "__main__":
    export_idaview()