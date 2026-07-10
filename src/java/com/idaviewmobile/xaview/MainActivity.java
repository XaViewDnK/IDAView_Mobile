package com.idaviewmobile.xaview;

import android.app.Activity;
import android.app.AlertDialog;
import android.app.Dialog;
import android.app.ProgressDialog;
import android.content.Context;
import android.content.Intent;
import android.content.SharedPreferences;
import android.graphics.Canvas;
import android.graphics.Color;
import android.graphics.Paint;
import android.graphics.Path;
import android.graphics.RectF;
import android.graphics.Typeface;
import android.net.Uri;
import android.os.Bundle;
import android.os.Handler;
import android.os.Looper;
import android.text.Editable;
import android.text.Layout;
import android.text.Spannable;
import android.text.SpannableStringBuilder;
import android.text.TextPaint;
import android.text.TextWatcher;
import android.text.style.BackgroundColorSpan;
import android.text.style.CharacterStyle;
import android.text.style.ForegroundColorSpan;
import android.text.style.ReplacementSpan;
import android.text.style.UpdateAppearance;
import android.view.GestureDetector;
import android.view.Gravity;
import android.view.MotionEvent;
import android.view.ScaleGestureDetector;
import android.view.View;
import android.view.ViewGroup;
import android.view.Window;
import android.widget.BaseAdapter;
import android.widget.Button;
import android.widget.CheckBox;
import android.widget.EditText;
import android.widget.LinearLayout;
import android.widget.ListView;
import android.widget.PopupMenu;
import android.widget.TextView;
import android.widget.Toast;
import android.widget.ScrollView;
import android.util.LongSparseArray;
import android.content.ClipData;
import android.content.ClipboardManager;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.InputStream;
import java.io.InputStreamReader;
import java.io.OutputStream;
import java.io.RandomAccessFile;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Stack;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.zip.ZipEntry;
import java.util.zip.ZipInputStream;
import java.util.zip.ZipOutputStream;

public class MainActivity extends Activity {

    private static final int PICK_FILE_REQUEST = 1;
    private static final int LINES_PER_CHUNK = 100;

    private Button btnTabIda, btnTabHex, btnTabStr, btnTabFunc, btnMenu;
    private LinearLayout emptyLayout, stringsSearchBar;
    private EditText editStrSearch;
    private ListView listView;
    private IdaAdapter listAdapter;

    private int currentTab = 0; // 0 = IDA, 1 = Hex, 2 = Strings, 3 = Functions
    private boolean isSearchingStrings = false;
    private int idaScrollPos = 0;
    private int idaScrollTop = 0;
    private int hexScrollPos = 0;
    private int hexScrollTop = 0;
    private boolean isShowHexEnabled = false;

    private void switchTab(int newTab) {
        int oldTab = currentTab;
        if (currentTab == 0 && newTab != 0) {
            idaScrollPos = listView.getFirstVisiblePosition();
            View cv = listView.getChildAt(0);
            idaScrollTop = (cv == null) ? 0 : cv.getTop();
        } else if (currentTab == 1 && newTab != 1) {
            hexScrollPos = listView.getFirstVisiblePosition();
            View cv = listView.getChildAt(0);
            hexScrollTop = (cv == null) ? 0 : cv.getTop();
        }
        currentTab = newTab;
        updateTabs();
        
        if ((newTab == 0 || newTab == 1) && !highlightedAddress.isEmpty() && oldTab != newTab) {
            doJump(highlightedAddress, false);
        } else if (currentTab == 0) {
            listView.setSelectionFromTop(idaScrollPos, idaScrollTop);
        } else if (currentTab == 1) {
            listView.setSelectionFromTop(hexScrollPos, hexScrollTop);
        }
    }

    private LongArray idaOffsets = new LongArray();
    private LongArray hexOffsets = new LongArray();
    private LongArray strOffsets = new LongArray();
    private LongArray filteredStrOffsets = new LongArray();
    private LongArray funcOffsets = new LongArray();
    private LongArray filteredFuncOffsets = new LongArray();

    private File cacheIdaFile;
    private File cacheHexFile;
    private File cacheItemHexFile;
    private File cacheStrFile;
    private File cacheFilteredStrFile;
    private File cacheFuncFile;
    private File cacheFilteredFuncFile;
    private Uri currentFileUri;

    // Стек для возврата после Jump
    private Stack<String> jumpHistory = new Stack<>();

    // Используем кастомный примитивный Hash Map: скорость O(1) и никаких аллокаций объектов
    private LongMap xrefsToOffsets = new LongMap();
    private LongMap xrefsFromOffsets = new LongMap();

    private HashMap<String, String> pendingComments = new HashMap<>();
    private HashMap<String, String> pendingRenames = new HashMap<>();
    private HashSet<String> functionStarts = new HashSet<>();
    private HashMap<String, String> functionNameToAddr = new HashMap<>();

    private String highlightedAddress = "";
    private String selectedStrAddress = "";
    private int selectedColumnIndex = -1;

    private String lastSearchQuery = "";
    private ArrayList<String> selectedExportFunctions = new ArrayList<>();
    private int lastFoundLineIndex = -1;
    private Handler searchHandler = new Handler(Looper.getMainLooper());
    private Runnable searchRunnable;

    // --- Каскадные регулярки ---
    private static final Pattern patBlueBase = Pattern.compile("\\b[A-Za-z_][A-Za-z0-9_]*\\b|\\.[a-zA-Z0-9_]+|[\\(\\)\\[\\]\\+\\-,:=\\?]");
    private static final Pattern patNavyKey = Pattern.compile("\\b(mov|call|push|pop|test|jnz|jz|jmp|sub|add|ret|lea|cmp|nop|offset|dword|ptr|short|dd|db|dw|eax|ebx|ecx|edx|esi|edi|esp|ebp|al|ah|bl|bh|cl|ch|dl|dh|setz|movzx|rva|dup|align)\\b");
    private static final Pattern patNavyReg = Pattern.compile("\\b(cs|ds|es|fs|gs|ss)\\b");
    private static final Pattern patNavyPunct = Pattern.compile("[\\(\\)\\[\\]\\+\\-,:=\\?]");
    private static final Pattern patNavyLabels = Pattern.compile("\\b(loc_[0-9A-Fa-f]+|off_[0-9A-Fa-f]+|word_[0-9A-Fa-f]+|dword_[0-9A-Fa-f]+|byte_[0-9A-Fa-f]+)\\b");
    private static final Pattern patNavyOffsetArg = Pattern.compile("(?:offset|rva)\\s+([A-Za-z_][A-Za-z0-9_]*)");
    private static final Pattern patNavyDataDef = Pattern.compile("(?:^|\\s)([A-Za-z_][A-Za-z0-9_]*)\\s+(?:db|dw|dd|dup)\\b");
    private static final Pattern patGreenVar = Pattern.compile("\\b(var_[0-9A-Fa-f]+|arg_[0-9A-Fa-f]+|lp[A-Za-z0-9_]+)\\b");
    private static final Pattern patGreenNum = Pattern.compile("\\b([0-9]+[0-9A-Fa-f]*h?|0x[0-9A-Fa-f]+)\\b");
    private static final Pattern patStr = Pattern.compile("('[^']*'|\"[^\"]*\")");
    private static final Pattern patPink = Pattern.compile("(?:call\\s+ds:|jmp\\s+ds:|extrn\\s+|(?:rva\\s+(?=[A-Z])))([A-Za-z_][A-Za-z0-9_]*)");
    private static final Pattern patAddr = Pattern.compile("^\\s*[a-zA-Z0-9_\\.\\-]+:([0-9A-Fa-f]+)");
    private static final Pattern patDirectives = Pattern.compile("\\b(assume|segment|ends|endp|proc|public|end)\\b");

    static class Xref {
        String fromAddr, toAddr, type, fromName, toName;
        Xref(String fA, String tA, String ty, String fN, String tN) {
            fromAddr=fA; toAddr=tA; type=ty; fromName=fN; toName=tN;
        }
    }

    @Override
    protected void onCreate(Bundle savedInstanceState) {
        super.onCreate(savedInstanceState);
        requestWindowFeature(Window.FEATURE_NO_TITLE);
        if (getActionBar() != null) getActionBar().hide();

        LinearLayout rootLayout = new LinearLayout(this);
        rootLayout.setOrientation(LinearLayout.VERTICAL);
        rootLayout.setBackgroundColor(Color.WHITE);
        rootLayout.setLayoutParams(new ViewGroup.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));

        int tabHeight = (int) (28 * getResources().getDisplayMetrics().density);
        LinearLayout topBar = new LinearLayout(this);
        topBar.setOrientation(LinearLayout.HORIZONTAL);
        topBar.setBackgroundColor(Color.parseColor("#E0E0E0"));

        LinearLayout tabLayout = new LinearLayout(this);
        tabLayout.setOrientation(LinearLayout.HORIZONTAL);
        tabLayout.setLayoutParams(new LinearLayout.LayoutParams(0, tabHeight, 1));

        btnTabIda = new Button(this);
        btnTabIda.setText("IDA View");
        btnTabIda.setTextSize(12);
        btnTabIda.setPadding(0, 0, 0, 0);
        btnTabIda.setLayoutParams(new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.MATCH_PARENT, 1));

        btnTabHex = new Button(this);
        btnTabHex.setText("Hex View");
        btnTabHex.setTextSize(12);
        btnTabHex.setPadding(0, 0, 0, 0);
        btnTabHex.setLayoutParams(new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.MATCH_PARENT, 1));

        btnTabStr = new Button(this);
        btnTabStr.setText("Strings");
        btnTabStr.setTextSize(12);
        btnTabStr.setPadding(0, 0, 0, 0);
        btnTabStr.setLayoutParams(new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.MATCH_PARENT, 1));

        btnTabFunc = new Button(this);
        btnTabFunc.setText("Functions");
        btnTabFunc.setTextSize(12);
        btnTabFunc.setPadding(0, 0, 0, 0);
        btnTabFunc.setLayoutParams(new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.MATCH_PARENT, 1));

        tabLayout.addView(btnTabIda);
        tabLayout.addView(btnTabHex);
        tabLayout.addView(btnTabStr);
        tabLayout.addView(btnTabFunc);

        btnMenu = new Button(this);
        btnMenu.setText("⋮");
        btnMenu.setTextSize(18);
        btnMenu.setPadding(20, 0, 20, 0);
        btnMenu.setBackgroundColor(Color.TRANSPARENT);
        btnMenu.setLayoutParams(new LinearLayout.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.MATCH_PARENT));
        btnMenu.setOnClickListener(v -> showPopupMenu());

        topBar.addView(tabLayout);
        topBar.addView(btnMenu);
        rootLayout.addView(topBar);

        listView = new ListView(this);
        listView.setLayoutParams(new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 0, 1));
        listView.setDivider(null);
        listView.setDividerHeight(0);
        listView.setFastScrollEnabled(true);
        listView.setDescendantFocusability(ViewGroup.FOCUS_AFTER_DESCENDANTS);
        listView.setItemsCanFocus(true);

        emptyLayout = new LinearLayout(this);
        emptyLayout.setOrientation(LinearLayout.VERTICAL);
        emptyLayout.setGravity(Gravity.CENTER);
        emptyLayout.setLayoutParams(new ViewGroup.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, ViewGroup.LayoutParams.MATCH_PARENT));

        Button btnOpen = new Button(this);
        btnOpen.setText("Open .IDAVIEW File");
        btnOpen.setOnClickListener(v -> openFilePicker());
        emptyLayout.addView(btnOpen);

        ((ViewGroup)listView.getParent() != null ? (ViewGroup)listView.getParent() : rootLayout).addView(emptyLayout);
        listView.setEmptyView(emptyLayout);
        rootLayout.addView(listView);

        stringsSearchBar = new LinearLayout(this);
        stringsSearchBar.setOrientation(LinearLayout.HORIZONTAL);
        stringsSearchBar.setBackgroundColor(Color.parseColor("#F5F5F5"));
        stringsSearchBar.setPadding(16, 16, 16, 16);
        stringsSearchBar.setVisibility(View.GONE);

        Button btnResetSearch = new Button(this);
        btnResetSearch.setText("✖");
        btnResetSearch.setTextColor(Color.parseColor("#00A2E8"));
        btnResetSearch.setBackgroundColor(Color.TRANSPARENT);
        btnResetSearch.setOnClickListener(v -> resetStringsSearch());

        editStrSearch = new EditText(this);
        editStrSearch.setLayoutParams(new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1));
        editStrSearch.setHint("Search strings...");
        editStrSearch.setSingleLine(true);
        editStrSearch.addTextChangedListener(new TextWatcher() {
            @Override public void beforeTextChanged(CharSequence s, int start, int count, int after) {}
            @Override public void onTextChanged(CharSequence s, int start, int before, int count) {
                if (searchRunnable != null) searchHandler.removeCallbacks(searchRunnable);
                searchRunnable = () -> filterStringsAsync(s.toString());
                searchHandler.postDelayed(searchRunnable, 300);
            }
            @Override public void afterTextChanged(Editable s) {}
        });

        stringsSearchBar.addView(btnResetSearch);
        stringsSearchBar.addView(editStrSearch);
        rootLayout.addView(stringsSearchBar);

        setContentView(rootLayout);

        btnTabIda.setOnClickListener(v -> switchTab(0));
        btnTabHex.setOnClickListener(v -> switchTab(1));
        btnTabStr.setOnClickListener(v -> switchTab(2));
        btnTabFunc.setOnClickListener(v -> switchTab(3));

        cacheIdaFile = new File(getCacheDir(), "ida.lst");
        cacheHexFile = new File(getCacheDir(), "hex_view.txt");
        cacheStrFile = new File(getCacheDir(), "strings.txt");
        cacheFilteredStrFile = new File(getCacheDir(), "strings_filtered.txt");
        cacheFuncFile = new File(getCacheDir(), "functions.txt");
        cacheFilteredFuncFile = new File(getCacheDir(), "functions_filtered.txt");

        listAdapter = new IdaAdapter();
        listView.setAdapter(listAdapter);

        if (savedInstanceState == null) {
            if (android.os.Build.VERSION.SDK_INT >= 23 && checkSelfPermission(android.Manifest.permission.READ_EXTERNAL_STORAGE) != android.content.pm.PackageManager.PERMISSION_GRANTED) {
                requestPermissions(new String[]{android.Manifest.permission.READ_EXTERNAL_STORAGE, android.Manifest.permission.WRITE_EXTERNAL_STORAGE}, 100);
            } else {
                openFilePicker();
            }
        }
    }

    @Override
    public void onRequestPermissionsResult(int requestCode, String[] permissions, int[] grantResults) {
        super.onRequestPermissionsResult(requestCode, permissions, grantResults);
        if (requestCode == 100) {
            // Запускаем выбор файла в любом случае. 
            // На некоторых прошивках ACTION_OPEN_DOCUMENT может работать и без полных прав, 
            // но сам факт запроса часто инициализирует нужные системные привязки к памяти.
            openFilePicker();
        }
    }

    private void showPopupMenu() {
        PopupMenu popup = new PopupMenu(this, btnMenu);
        popup.getMenu().add(0, 5, 0, "Save");
        if (!jumpHistory.isEmpty()) {
            popup.getMenu().add(0, 6, 0, "Jump Back");
        }
        if (currentTab == 0) {
            popup.getMenu().add(0, 8, 0, isShowHexEnabled ? "Visual: Hide HEX" : "Visual: Show HEX");
            popup.getMenu().add(0, 7, 0, "Export functions list");
            popup.getMenu().add(0, 1, 0, "Jump: to address");
            popup.getMenu().add(0, 2, 0, "Search: text");
            popup.getMenu().add(0, 3, 0, "Search: next next");
            popup.getMenu().add(0, 4, 0, "Search: immediate value");
        } else if (currentTab == 1) {
            popup.getMenu().add(0, 1, 0, "Jump: to address");
        } else {
            popup.getMenu().add(0, 2, 0, "Search: text");
            popup.getMenu().add(0, 3, 0, "Search: next next");
        }

        popup.setOnMenuItemClickListener(item -> {
            switch(item.getItemId()) {
                case 8: 
                    toggleShowHex();
                    break;
                case 7: showExportFunctionsDialog(); break;
                case 1: showJumpDialog(); break;
                case 2:
                    if (currentTab == 0) showIdaSearchDialog(false);
                    else activateStringsSearch();
                    break;
                case 3:
                    if (currentTab == 0) performSearchNext();
                    else Toast.makeText(this, "Next search in lists is live via filtering", Toast.LENGTH_SHORT).show();
                    break;
                case 4: showIdaSearchDialog(true); break;
                case 5: saveChangesToFile(); break;
                case 6: goBackHistory(); break;
            }
            return true;
        });
        popup.show();
    }

        private void toggleShowHex() {
        isShowHexEnabled = !isShowHexEnabled;
        listAdapter.notifyDataSetChanged();
    }

    private void goBackHistory() {
        if (!jumpHistory.isEmpty()) {
            String prevAddr = jumpHistory.pop();
            doJump(prevAddr, false);
        }
    }

    private void saveChangesToFile() {
        if (currentFileUri == null) return;
        ProgressDialog pd = ProgressDialog.show(this, "Saving", "Writing changes to file...", true, false);
        new Thread(() -> {
            try {
                File tempZip = new File(getCacheDir(), "temp.IDAVIEW");
                ZipOutputStream zos = new ZipOutputStream(new FileOutputStream(tempZip));

                if (cacheStrFile.exists()) {
                    zos.putNextEntry(new ZipEntry("strings.txt"));
                    FileInputStream fisStr = new FileInputStream(cacheStrFile);
                    byte[] buf = new byte[8192]; int len;
                    while ((len = fisStr.read(buf)) > 0) zos.write(buf, 0, len);
                    fisStr.close();
                    zos.closeEntry();
                }
                
                // Перепаковка xrefs.txt (если нужно сохранить без изменений)
                File xrefsFile = new File(getCacheDir(), "xrefs.txt");
                if (xrefsFile.exists()) {
                    zos.putNextEntry(new ZipEntry("xrefs.txt"));
                    FileInputStream fisXref = new FileInputStream(xrefsFile);
                    byte[] buf = new byte[8192]; int len;
                    while ((len = fisXref.read(buf)) > 0) zos.write(buf, 0, len);
                    fisXref.close();
                    zos.closeEntry();
                }

                if (cacheIdaFile.exists()) {
                    zos.putNextEntry(new ZipEntry("ida.lst"));
                    BufferedReader br = new BufferedReader(new InputStreamReader(new FileInputStream(cacheIdaFile)));
                    String line;
                    while ((line = br.readLine()) != null) {
                        for (Map.Entry<String, String> entry : pendingRenames.entrySet()) {
                            line = line.replaceAll("(?<![a-zA-Z0-9_])" + entry.getKey() + "(?![a-zA-Z0-9_])", entry.getValue());
                        }
                        Matcher mAddr = patAddr.matcher(line);
                        if (mAddr.find()) {
                            String addr = mAddr.group(1);
                            if (pendingComments.containsKey(addr)) {
                                line = line + " ; " + pendingComments.get(addr);
                            }
                        }
                        line += "\n";
                        zos.write(line.getBytes("UTF-8"));
                    }
                    br.close();
                    zos.closeEntry();
                }
                zos.close();

                OutputStream osUri = getContentResolver().openOutputStream(currentFileUri, "wt");
                if (osUri != null) {
                    FileInputStream tempFis = new FileInputStream(tempZip);
                    byte[] buf = new byte[8192]; int len;
                    while ((len = tempFis.read(buf)) > 0) osUri.write(buf, 0, len);
                    tempFis.close();
                    osUri.close();
                }

                new Handler(Looper.getMainLooper()).post(() -> {
                    pd.dismiss();
                    pendingComments.clear();
                    pendingRenames.clear();
                    Toast.makeText(MainActivity.this, "Successfully saved!", Toast.LENGTH_LONG).show();
                    processIdaViewFile(currentFileUri);
                });
            } catch (Exception e) {
                new Handler(Looper.getMainLooper()).post(() -> {
                    pd.dismiss();
                    Toast.makeText(MainActivity.this, "Error saving: " + e.getMessage(), Toast.LENGTH_LONG).show();
                });
            }
        }).start();
    }

    private void showJumpDialog() {
        AlertDialog.Builder builder = new AlertDialog.Builder(this);
        builder.setTitle("Jump to address or function");
        final EditText input = new EditText(this);
        input.setHint("e.g. 00401000 or _start");
        builder.setView(input);
        builder.setPositiveButton("OK", (dialog, which) -> jumpToAddress(input.getText().toString().trim()));
        builder.setNegativeButton("Cancel", null);
        builder.show();
    }

    private void jumpToAddress(String address) {
        if (address.isEmpty()) return;
        if (!highlightedAddress.isEmpty() && !address.equals(highlightedAddress)) {
            jumpHistory.push(highlightedAddress);
        }
        doJump(address, true);
    }

    private void doJump(String address, boolean showToastNotFound) {
        ProgressDialog pd = new ProgressDialog(this);
        pd.setTitle("Jumping");
        pd.setMessage("Please wait...");
        pd.setIndeterminate(true);
        pd.setCancelable(true); // Разрешаем закрытие системной кнопкой "Назад"
        pd.setCanceledOnTouchOutside(false); // Но запрещаем закрытие случайным тапом мимо окна
        pd.show();
        
        final boolean[] isCancelled = {false};
        pd.setOnCancelListener(dialog -> isCancelled[0] = true);

        new Thread(() -> {
            try {
                File fileToSearch = (currentTab == 1) ? cacheHexFile : cacheIdaFile;
                BufferedReader br = new BufferedReader(new InputStreamReader(new FileInputStream(fileToSearch)));
                String line;
                int lineCount = 0;
                int targetLine = -1;
                
                long targetVal = -1;
                String hex8 = null, hex16 = null;
                String searchQuery = address.trim();
                String rawUpper = searchQuery.toUpperCase();

                // Проверяем, ввел ли пользователь имя функции (с учетом возможных Rename в текущей сессии)
                String originalName = searchQuery;
                for (Map.Entry<String, String> entry : pendingRenames.entrySet()) {
                    if (entry.getValue().equals(searchQuery)) {
                        originalName = entry.getKey();
                        break;
                    }
                }
                
                // Если это имя функции, заменяем строку поиска на её Hex-адрес
                if (functionNameToAddr.containsKey(originalName)) {
                    rawUpper = functionNameToAddr.get(originalName).toUpperCase();
                }
                
                try {
                    // Пытаемся понять, ввел ли пользователь валидный Hex-адрес (или мы его подменили)
                    targetVal = Long.parseLong(rawUpper, 16);
                    hex8 = String.format("%08X", targetVal);   // Формат IDA для 32-bit (с нулями)
                    hex16 = String.format("%016X", targetVal); // Формат IDA для 64-bit (с нулями)
                } catch (NumberFormatException ignored) {}

                while ((line = br.readLine()) != null) {
                    if (isCancelled[0]) break; // Мгновенно прерываем поиск, если нажата кнопка "Назад"

                    if (targetVal != -1) {
                        if (currentTab == 1) {
                            int tabIdx = line.indexOf('\t');
                            if (tabIdx > 0) {
                                try {
                                    if (Long.parseLong(line.substring(0, tabIdx).trim(), 16) >= targetVal) {
                                        targetLine = lineCount;
                                        break;
                                    }
                                } catch (Exception ignored) {}
                            }
                        } else {
                            if (line.contains(hex8) || line.contains(hex16) || line.contains(rawUpper)) {
                                Matcher mAddr = patAddr.matcher(line);
                                if (mAddr.find()) {
                                    try {
                                        if (Long.parseLong(mAddr.group(1), 16) == targetVal) {
                                            targetLine = lineCount;
                                            break;
                                        }
                                    } catch (NumberFormatException ignored) {}
                                }
                            }
                        }
                    } else {
                        if (currentTab != 1 && line.contains(address)) {
                            targetLine = lineCount;
                            break;
                        }
                    }
                    lineCount++;
                }
                br.close();

                final int finalTargetLine = targetLine;
                new Handler(Looper.getMainLooper()).post(() -> {
                    if (pd.isShowing()) pd.dismiss();
                    if (isCancelled[0]) return; // Выходим без изменения UI и смены вкладок

                    if (finalTargetLine != -1) {
                        highlightedAddress = address;
                        
                        // Если мы прыгаем из списка строк или функций (вкладки 2 и 3) - кидаем в IDA View
                        // Если прыжок вызван переключением или поиском внутри IDA/Hex, остаемся в целевой вкладке
                        if (currentTab != 0 && currentTab != 1) {
                            currentTab = 0;
                        }
                        updateTabs();
                        
                        int finalChunk = finalTargetLine / LINES_PER_CHUNK;
                        int lineInChunk = finalTargetLine % LINES_PER_CHUNK;
                        float density = getResources().getDisplayMetrics().density;
                        int yOffset = (int) (lineInChunk * 15 * density);
                        
                        if (currentTab == 0) {
                            idaScrollPos = finalChunk;
                            idaScrollTop = (listView.getHeight() / 2) - yOffset;
                            listView.setSelectionFromTop(idaScrollPos, idaScrollTop);
                        } else if (currentTab == 1) {
                            hexScrollPos = finalChunk;
                            hexScrollTop = (listView.getHeight() / 2) - yOffset;
                            listView.setSelectionFromTop(hexScrollPos, hexScrollTop);
                        }
                    } else if (showToastNotFound) {
                        Toast.makeText(MainActivity.this, "Address not found in " + (currentTab == 1 ? "Hex View" : "IDA View"), Toast.LENGTH_SHORT).show();
                    }
                });
            } catch (Exception e) {
                new Handler(Looper.getMainLooper()).post(() -> {
                    if (pd.isShowing()) pd.dismiss();
                });
            }
        }).start();
    }

    private void showExportFunctionsDialog() {
        AlertDialog.Builder builder = new AlertDialog.Builder(this);
        builder.setTitle("Export Functions List");

        LinearLayout root = new LinearLayout(this);
        root.setOrientation(LinearLayout.VERTICAL);
        root.setPadding(40, 40, 40, 40);

        // Строка ввода и кнопка "+"
        LinearLayout inputRow = new LinearLayout(this);
        inputRow.setOrientation(LinearLayout.HORIZONTAL);
        inputRow.setGravity(Gravity.CENTER_VERTICAL);
        
        final EditText input = new EditText(this);
        input.setHint("Function name (e.g. _start)");
        input.setSingleLine(true);
        input.setLayoutParams(new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1));
        
        Button btnAdd = new Button(this);
        btnAdd.setText("+");
        btnAdd.setTextSize(20);
        btnAdd.setLayoutParams(new LinearLayout.LayoutParams(ViewGroup.LayoutParams.WRAP_CONTENT, ViewGroup.LayoutParams.WRAP_CONTENT));

        inputRow.addView(input);
        inputRow.addView(btnAdd);
        root.addView(inputRow);

        // Прокручиваемый список
        ScrollView scroll = new ScrollView(this);
        scroll.setLayoutParams(new LinearLayout.LayoutParams(ViewGroup.LayoutParams.MATCH_PARENT, 0, 1));
        scroll.setPadding(0, 20, 0, 0);
        final LinearLayout listLayout = new LinearLayout(this);
        listLayout.setOrientation(LinearLayout.VERTICAL);
        scroll.addView(listLayout);
        root.addView(scroll);

        Runnable updateListUI = new Runnable() {
            @Override
            public void run() {
                listLayout.removeAllViews();
                for (int i = 0; i < selectedExportFunctions.size(); i++) {
                    final String funcName = selectedExportFunctions.get(i);
                    LinearLayout row = new LinearLayout(MainActivity.this);
                    row.setOrientation(LinearLayout.HORIZONTAL);
                    row.setGravity(Gravity.CENTER_VERTICAL);
                    row.setPadding(0, 10, 0, 10);
                    
                    TextView tv = new TextView(MainActivity.this);
                    tv.setText(funcName);
                    tv.setTextColor(Color.BLACK);
                    tv.setTextSize(16);
                    tv.setLayoutParams(new LinearLayout.LayoutParams(0, ViewGroup.LayoutParams.WRAP_CONTENT, 1));
                    
                    Button btnRemove = new Button(MainActivity.this);
                    btnRemove.setText("❌");
                    btnRemove.setTextColor(Color.RED);
                    btnRemove.setBackgroundColor(Color.TRANSPARENT);
                    btnRemove.setPadding(10, 0, 10, 0);
                    
                    btnRemove.setOnClickListener(v -> {
                        selectedExportFunctions.remove(funcName);
                        this.run();
                    });
                    
                    row.addView(tv);
                    row.addView(btnRemove);
                    listLayout.addView(row);
                }
            }
        };
        
        btnAdd.setOnClickListener(v -> {
            String name = input.getText().toString().trim();
            if (!name.isEmpty() && !selectedExportFunctions.contains(name)) {
                selectedExportFunctions.add(name);
                input.setText("");
                updateListUI.run();
            }
        });

        updateListUI.run();
        builder.setView(root);
        
        builder.setPositiveButton("Export", (dialog, which) -> {
            // Запрос разрешений без AndroidX (чистый API 23+)
            if (android.os.Build.VERSION.SDK_INT >= 23) {
                if (checkSelfPermission(android.Manifest.permission.WRITE_EXTERNAL_STORAGE) != android.content.pm.PackageManager.PERMISSION_GRANTED) {
                    requestPermissions(new String[]{android.Manifest.permission.WRITE_EXTERNAL_STORAGE}, 2);
                    Toast.makeText(this, "Permission required. Please grant and click Export again.", Toast.LENGTH_LONG).show();
                    return;
                }
            }
            exportFunctionsListToFile(new ArrayList<>(selectedExportFunctions));
        });
        builder.setNegativeButton("Cancel", null);
        builder.show();
    }

    private String extractFunctionContentSync(String targetAddr) {
        try {
            BufferedReader br = new BufferedReader(new InputStreamReader(new FileInputStream(cacheIdaFile)));
            String line;
            StringBuilder sb = new StringBuilder();
            boolean capturing = false;
            boolean passedEndMarker = false;
            int consecutiveEmptyLines = 0;
            String upperTarget = targetAddr.toUpperCase();

            while ((line = br.readLine()) != null) {
                if (!capturing) {
                    // Быстрый фильтр (String.contains в сотни раз быстрее Regex)
                    if (line.contains(upperTarget)) {
                        Matcher mAddr = patAddr.matcher(line);
                        if (mAddr.find() && mAddr.group(1).equalsIgnoreCase(targetAddr)) {
                            // Быстрый срез вместо тяжелого replaceFirst
                            String cleanContent = line.substring(mAddr.end()).trim();
                            if (cleanContent.isEmpty() || cleanContent.equals(";") || cleanContent.contains("S U B R O U T I N E")) continue; 
                            capturing = true;
                            sb.append(line).append("\n");
                        }
                    }
                } else {
                    if (line.contains("; =============== S U B R O U T I N E") || line.contains("proc near")) {
                        if (passedEndMarker) break; 
                    }
                    
                    String lineContent = line;
                    Matcher mAddr = patAddr.matcher(line);
                    if (mAddr.find()) {
                        lineContent = line.substring(mAddr.end()).trim();
                    } else {
                        lineContent = lineContent.trim();
                    }

                    if (lineContent.isEmpty() || lineContent.equals(";")) consecutiveEmptyLines++;
                    else consecutiveEmptyLines = 0;

                    if (passedEndMarker && consecutiveEmptyLines >= 2) break;

                    sb.append(line).append("\n");

                    if (line.contains("; End of function") || line.contains("endp")) passedEndMarker = true;
                    if (passedEndMarker && line.contains("; } // starts at")) break; 
                    if (passedEndMarker && (line.contains("Segment type:") || line.contains("Section "))) break;
                }
            }
            br.close();
            String res = sb.toString().trim();
            res = res.replaceAll("(\\n\\s*[a-zA-Z0-9_\\.\\-]+:[0-9A-Fa-f]+\\s*)+$", "");
            return res;
        } catch (Exception e) {
            return "";
        }
    }

    private void exportFunctionsListToFile(List<String> functions) {
        if (functions.isEmpty()) {
            Toast.makeText(this, "List is empty", Toast.LENGTH_SHORT).show();
            return;
        }
        
        ProgressDialog pd = ProgressDialog.show(this, "Exporting", "Writing functions to file...", true, false);
        new Thread(() -> {
            try {
                String baseName = "IDA_Export";
                if (currentFileUri != null) {
                    try {
                        // Правильный способ достать оригинальное имя файла из Content URI
                        android.database.Cursor cursor = getContentResolver().query(currentFileUri, null, null, null, null);
                        if (cursor != null && cursor.moveToFirst()) {
                            int nameIndex = cursor.getColumnIndex(android.provider.OpenableColumns.DISPLAY_NAME);
                            if (nameIndex != -1) {
                                baseName = cursor.getString(nameIndex);
                                // Убираем расширение файла (.IDAVIEW или .zip)
                                int dotIndex = baseName.lastIndexOf('.');
                                if (dotIndex > 0) baseName = baseName.substring(0, dotIndex);
                            }
                            cursor.close();
                        }
                    } catch (Exception ignore) {}
                    
                    // Жесткая зачистка: убираем любые спецсимволы (вроде двоеточий от msf:), оставляя только буквы, цифры, минус и нижнее подчеркивание
                    baseName = baseName.replaceAll("[^a-zA-Z0-9_\\-]", "_");
                }
                
                File dir = new File(android.os.Environment.getExternalStorageDirectory(), "IDAViewMobile");
                if (!dir.exists()) dir.mkdirs();
                File outFile = new File(dir, baseName + "_selected_functions_list.txt");
                
                FileOutputStream fos = new FileOutputStream(outFile);
                
                boolean isFirst = true;
                for (int i = 0; i < functions.size(); i++) {
                    String funcInput = functions.get(i);
                    String targetAddr = "";
                    
                    // Учет возможных ренеймов из текущей сессии
                    String originalName = funcInput;
                    for (Map.Entry<String, String> entry : pendingRenames.entrySet()) {
                        if (entry.getValue().equals(funcInput)) {
                            originalName = entry.getKey();
                            break;
                        }
                    }
                    
                    if (functionNameToAddr.containsKey(originalName)) {
                        targetAddr = functionNameToAddr.get(originalName);
                    } else {
                        // Фолбэк на случай если ввели напрямую hex адрес
                        try {
                            long val = Long.parseLong(funcInput, 16);
                            targetAddr = String.format("%08X", val);
                            if (!functionStarts.contains(targetAddr)) {
                                targetAddr = String.format("%016X", val);
                            }
                        } catch (Exception ignored) {}
                    }
                    
                    if (!targetAddr.isEmpty()) {
                        String content = extractFunctionContentSync(targetAddr);
                        if (!content.isEmpty()) {
                            // Применяем актуальные комментарии и ренеймы к блоку кода перед сохранением
                            content = applyPendingChanges(content);
                            if (!isFirst) {
                                fos.write("\n\n=======================\n\n".getBytes("UTF-8"));
                            }
                            fos.write(content.getBytes("UTF-8"));
                            isFirst = false;
                        }
                    }
                }
                fos.close();
                
                new Handler(Looper.getMainLooper()).post(() -> {
                    pd.dismiss();
                    Toast.makeText(MainActivity.this, "Exported to: " + outFile.getAbsolutePath(), Toast.LENGTH_LONG).show();
                    selectedExportFunctions.clear();
                });
            } catch (Exception e) {
                new Handler(Looper.getMainLooper()).post(() -> {
                    pd.dismiss();
                    Toast.makeText(MainActivity.this, "Error exporting: " + e.getMessage(), Toast.LENGTH_LONG).show();
                });
            }
        }).start();
    }

    // --- IDA / Strings Search ---
    private void showIdaSearchDialog(boolean immediate) {
        AlertDialog.Builder builder = new AlertDialog.Builder(this);
        builder.setTitle(immediate ? "Search immediate value" : "Search text");
        LinearLayout layout = new LinearLayout(this);
        layout.setOrientation(LinearLayout.VERTICAL);
        layout.setPadding(40, 20, 40, 20);
        final EditText input = new EditText(this);
        input.setText(lastSearchQuery);
        layout.addView(input);
        SharedPreferences prefs = getSharedPreferences("ida_prefs", Context.MODE_PRIVATE);
        final CheckBox cbMatchCase = new CheckBox(this);
        cbMatchCase.setText("Match case");
        cbMatchCase.setChecked(prefs.getBoolean("match_case", false));
        layout.addView(cbMatchCase);
        final CheckBox cbSearchUp = new CheckBox(this);
        cbSearchUp.setText("Search Up");
        cbSearchUp.setChecked(prefs.getBoolean("search_up", false));
        layout.addView(cbSearchUp);
        builder.setView(layout);
        builder.setPositiveButton("OK", (dialog, which) -> {
            boolean mCase = cbMatchCase.isChecked();
            boolean sUp = cbSearchUp.isChecked();
            prefs.edit().putBoolean("match_case", mCase).putBoolean("search_up", sUp).apply();
            lastSearchQuery = input.getText().toString();
            searchInIdaFile(lastSearchQuery, mCase, sUp, false);
        });
        builder.setNegativeButton("Cancel", null);
        builder.show();
    }

    private void performSearchNext() {
        if (lastSearchQuery.isEmpty()) return;
        SharedPreferences prefs = getSharedPreferences("ida_prefs", Context.MODE_PRIVATE);
        searchInIdaFile(lastSearchQuery, prefs.getBoolean("match_case", false), prefs.getBoolean("search_up", false), true);
    }

    private void searchInIdaFile(String query, boolean matchCase, boolean searchUp, boolean isNext) {
        if (query.isEmpty()) return;
        ProgressDialog pd = ProgressDialog.show(this, "Searching", "Please wait...", true, false);
        new Thread(() -> {
            try {
                BufferedReader br = new BufferedReader(new InputStreamReader(new FileInputStream(cacheIdaFile)));
                String line;
                int lineIdx = 0;
                int foundLine = -1;
                String q = matchCase ? query : query.toLowerCase();

                while ((line = br.readLine()) != null) {
                    String checkLine = matchCase ? line : line.toLowerCase();
                    if (checkLine.contains(q)) {
                        if (searchUp) {
                            if (!isNext || lineIdx < lastFoundLineIndex) { foundLine = lineIdx; } 
                            else if (isNext && lineIdx >= lastFoundLineIndex) { break; }
                        } else {
                            if (!isNext || lineIdx > lastFoundLineIndex) { foundLine = lineIdx; break; }
                        }
                    }
                    lineIdx++;
                }
                br.close();

                final int finalFound = foundLine;
                new Handler(Looper.getMainLooper()).post(() -> {
                    pd.dismiss();
                    if (finalFound != -1) {
                        lastFoundLineIndex = finalFound;
                        listView.setSelection(finalFound / LINES_PER_CHUNK);
                    } else {
                        Toast.makeText(MainActivity.this, "String not found", Toast.LENGTH_SHORT).show();
                        if (!isNext) lastFoundLineIndex = -1;
                    }
                });
            } catch (Exception e) {
                new Handler(Looper.getMainLooper()).post(() -> pd.dismiss());
            }
        }).start();
    }

    private void activateStringsSearch() { stringsSearchBar.setVisibility(View.VISIBLE); editStrSearch.requestFocus(); }
    private void resetStringsSearch() {
        editStrSearch.setText(""); stringsSearchBar.setVisibility(View.GONE);
        isSearchingStrings = false; listAdapter.notifyDataSetChanged();
    }

    private void filterStringsAsync(String query) {
        if (query.isEmpty()) {
            isSearchingStrings = false;
            new Handler(Looper.getMainLooper()).post(() -> listAdapter.notifyDataSetChanged());
            return;
        }
        new Thread(() -> {
            try {
                File sourceFile = (currentTab == 2) ? cacheFuncFile : cacheStrFile;
                File targetFile = (currentTab == 2) ? cacheFilteredFuncFile : cacheFilteredStrFile;
                LongArray targetOffsets = (currentTab == 2) ? filteredFuncOffsets : filteredStrOffsets;
                
                BufferedReader br = new BufferedReader(new InputStreamReader(new FileInputStream(sourceFile)));
                FileOutputStream fos = new FileOutputStream(targetFile);
                targetOffsets.clear(); targetOffsets.add(0);
                String line; String lowerQuery = query.toLowerCase();
                long byteCounter = 0; int lineCounter = 0;
                while ((line = br.readLine()) != null) {
                    if (lineCounter == 0 || line.toLowerCase().contains(lowerQuery)) {
                        String outLine = line + "\n";
                        byte[] bytes = outLine.getBytes("UTF-8");
                        fos.write(bytes);
                        lineCounter++;
                        if (lineCounter > 1 && (lineCounter - 1) % LINES_PER_CHUNK == 0) targetOffsets.add(byteCounter + bytes.length);
                        byteCounter += bytes.length;
                    }
                }
                targetOffsets.add(byteCounter);
                fos.close(); br.close();
                new Handler(Looper.getMainLooper()).post(() -> {
                    isSearchingStrings = true; listAdapter.notifyDataSetChanged();
                });
            } catch (Exception e) {}
        }).start();
    }

    private void openFilePicker() {
        Intent intent = new Intent(Intent.ACTION_OPEN_DOCUMENT);
        intent.addCategory(Intent.CATEGORY_OPENABLE);
        intent.setType("*/*");
        startActivityForResult(intent, PICK_FILE_REQUEST);
    }

    @Override
    protected void onActivityResult(int requestCode, int resultCode, Intent data) {
        super.onActivityResult(requestCode, resultCode, data);
        if (requestCode == PICK_FILE_REQUEST && resultCode == RESULT_OK && data != null) {
            currentFileUri = data.getData();
            processIdaViewFile(currentFileUri);
        }
    }

    private void processIdaViewFile(final Uri uri) {
        ProgressDialog pd = ProgressDialog.show(this, "Indexing Database", "Parsing IDA View & Xrefs...", true, false);
        new Thread(() -> {
            try {
                InputStream is = getContentResolver().openInputStream(uri);
                ZipInputStream zis = new ZipInputStream(is);
                ZipEntry entry;

                idaOffsets.clear(); hexOffsets.clear(); strOffsets.clear(); funcOffsets.clear();
                xrefsFromOffsets.clear(); xrefsToOffsets.clear();
                jumpHistory.clear();
                isShowHexEnabled = false;

                while ((entry = zis.getNextEntry()) != null) {
                    String name = entry.getName();
                    if (name.equals("xrefs.txt")) {
                        // Оптимизированный парсинг Xrefs: сохраняем только байтовые смещения
                        File xrFile = new File(getCacheDir(), "xrefs.txt");
                        FileOutputStream fosXref = new FileOutputStream(xrFile);
                        byte[] buf = new byte[65536]; int lenXref;
                        while ((lenXref = zis.read(buf)) > 0) fosXref.write(buf, 0, lenXref);
                        fosXref.close();

                        RandomAccessFile raf = new RandomAccessFile(xrFile, "r");
                        long fileOffset = 0;
                        long lineStartOffset = 0;
                        long currentFrom = 0;
                        long currentTo = 0;
                        int col = 0;
                        boolean inHex = true;
                        int bytesRead;

                        while ((bytesRead = raf.read(buf)) > 0) {
                            for (int i = 0; i < bytesRead; i++) {
                                byte b = buf[i];
                                if (b == '\n') {
                                    if (col >= 2) {
                                        xrefsFromOffsets.put(currentFrom, lineStartOffset);
                                        xrefsToOffsets.put(currentTo, lineStartOffset);
                                    }
                                    lineStartOffset = fileOffset + i + 1;
                                    col = 0; currentFrom = 0; currentTo = 0; inHex = true;
                                } else if (b == '\t') {
                                    col++;
                                    inHex = (col < 2);
                                } else if (inHex) {
                                    int val = -1;
                                    if (b >= '0' && b <= '9') val = b - '0';
                                    else if (b >= 'A' && b <= 'F') val = b - 'A' + 10;
                                    else if (b >= 'a' && b <= 'f') val = b - 'a' + 10;

                                    if (val != -1) {
                                        if (col == 0) currentFrom = (currentFrom << 4) | val;
                                        else if (col == 1) currentTo = (currentTo << 4) | val;
                                    }
                                }
                            }
                            fileOffset += bytesRead;
                        }
                        
                        // Обработка последней строки, если она не заканчивается переносом
                        if (col >= 2) {
                            xrefsFromOffsets.put(currentFrom, lineStartOffset);
                            xrefsToOffsets.put(currentTo, lineStartOffset);
                        }
                        raf.close();
                    } else if (name.equals("item_hex.txt")) {
                        cacheItemHexFile = new File(getCacheDir(), "item_hex.txt");
                        FileOutputStream fosItemHex = new FileOutputStream(cacheItemHexFile);
                        byte[] buf = new byte[65536]; 
                        int lenHex;
                        while ((lenHex = zis.read(buf)) > 0) fosItemHex.write(buf, 0, lenHex);
                        fosItemHex.close();
                    } else if (name.equals("ida.lst") || name.equals("hex_view.txt") || name.equals("strings.txt") || name.equals("functions.txt")) {
                        File targetFile = name.equals("ida.lst") ? cacheIdaFile : (name.equals("hex_view.txt") ? cacheHexFile : (name.equals("strings.txt") ? cacheStrFile : cacheFuncFile));
                        LongArray targetOffsets = name.equals("ida.lst") ? idaOffsets : (name.equals("hex_view.txt") ? hexOffsets : (name.equals("strings.txt") ? strOffsets : funcOffsets));
                        FileOutputStream fos = new FileOutputStream(targetFile);
                        long byteCounter = 0; int lineCounter = 0;
                        targetOffsets.add(0);
                        byte[] buffer = new byte[8192]; int len;
                        while ((len = zis.read(buffer)) > 0) {
                            fos.write(buffer, 0, len);
                            for (int i = 0; i < len; i++) {
                                if (buffer[i] == '\n') {
                                    lineCounter++;
                                    if (lineCounter % LINES_PER_CHUNK == 0) targetOffsets.add(byteCounter + i + 1);
                                }
                            }
                            byteCounter += len;
                        }
                        targetOffsets.add(byteCounter);
                        fos.close();
                    }
                    zis.closeEntry();
                }
                zis.close(); is.close();

                if (idaOffsets.size == 0 && hexOffsets.size == 0 && strOffsets.size == 0 && funcOffsets.size == 0) {
                    throw new Exception("Invalid file. The selected file is not a valid .IDAVIEW archive or cannot be read.");
                }

                try {
                    functionStarts.clear();
                    functionNameToAddr.clear();
                    if (cacheFuncFile.exists()) {
                        BufferedReader fbr = new BufferedReader(new InputStreamReader(new FileInputStream(cacheFuncFile)));
                        String fLine;
                        boolean firstLine = true;
                        while ((fLine = fbr.readLine()) != null) {
                            if (firstLine) { firstLine = false; continue; } // Пропускаем шапку
                            
                            // Избавляемся от тяжелого .split() внутри горячего цикла
                            int t1 = fLine.indexOf('\t');
                            if (t1 > 0) {
                                int t2 = fLine.indexOf('\t', t1 + 1);
                                if (t2 > t1) {
                                    String addrPart = fLine.substring(0, t1);
                                    int colon = addrPart.indexOf(':');
                                    if (colon >= 0) {
                                        String hexAddr = addrPart.substring(colon + 1);
                                        String funcName = fLine.substring(t2 + 1);
                                        functionStarts.add(hexAddr);
                                        functionNameToAddr.put(funcName, hexAddr);
                                    }
                                }
                            }
                        }
                        fbr.close();
                    }
                } catch (Exception ignored) {}

                new Handler(Looper.getMainLooper()).post(() -> {
                    pd.dismiss();
                    idaScrollPos = 0; idaScrollTop = 0;
                    switchTab(0);
                });
            } catch (Exception e) {
                new Handler(Looper.getMainLooper()).post(() -> {
                    pd.dismiss(); Toast.makeText(MainActivity.this, "Error: " + e.getMessage(), Toast.LENGTH_LONG).show();
                });
            }
        }).start();
    }

    private void updateTabs() {
        btnTabIda.setBackgroundColor(currentTab == 0 ? Color.LTGRAY : Color.TRANSPARENT);
        btnTabHex.setBackgroundColor(currentTab == 1 ? Color.LTGRAY : Color.TRANSPARENT);
        btnTabStr.setBackgroundColor(currentTab == 2 ? Color.LTGRAY : Color.TRANSPARENT);
        btnTabFunc.setBackgroundColor(currentTab == 3 ? Color.LTGRAY : Color.TRANSPARENT);
        stringsSearchBar.setVisibility((currentTab == 0 || currentTab == 1) ? View.GONE : (isSearchingStrings ? View.VISIBLE : View.GONE));
        editStrSearch.setHint(currentTab == 2 ? "Search strings..." : "Search functions...");
        
        // Жесткий сброс состояния ListView. Это заставит его забыть старые размеры 
        // и без конфликтов применить новую позицию прокрутки.
        listView.setAdapter(listAdapter);
    }

    private String extractWord(String line, int pos) {
        Matcher m = Pattern.compile("[a-zA-Z_][a-zA-Z0-9_]*").matcher(line);
        while (m.find()) {
            if (pos >= m.start() && pos <= m.end()) {
                String w = m.group();
                if (!patNavyKey.matcher(w).matches() && !patNavyReg.matcher(w).matches() && !patDirectives.matcher(w).matches()) return w;
            }
        }
        return "";
    }

    // --- Обновленное меню Long Tap ---
    private void showLongTapMenu(final String addr, final String word) {
        AlertDialog.Builder b = new AlertDialog.Builder(this);
        List<String> items = new ArrayList<>();
        items.add("Enter comment");
        if (!word.isEmpty()) items.add("Rename");
        if (!addr.isEmpty()) {
            if (currentTab == 0 && functionStarts.contains(addr)) items.add("Copy entire function");
            items.add("List xrefs to");
            items.add("List xrefs from");
            items.add("Xrefs graph to");
            items.add("Xrefs graph from");
        }
        
        b.setItems(items.toArray(new String[0]), (dialog, which) -> {
            String choice = items.get(which);
            if (choice.equals("Enter comment")) showCommentDialog(addr);
            else if (choice.equals("Rename")) showRenameDialog(word);
            else if (choice.equals("Copy entire function")) copyEntireFunction(addr);
            else if (choice.equals("List xrefs to")) showXrefsList(addr, true);
            else if (choice.equals("List xrefs from")) showXrefsList(addr, false);
            else if (choice.equals("Xrefs graph to")) showXrefsGraph(addr, true);
            else if (choice.equals("Xrefs graph from")) showXrefsGraph(addr, false);
        });
        b.show();
    }

    private void copyEntireFunction(String targetAddr) {
        ProgressDialog pd = ProgressDialog.show(this, "Copying", "Capturing function...", true, false);
        new Thread(() -> {
            try {
                BufferedReader br = new BufferedReader(new InputStreamReader(new FileInputStream(cacheIdaFile)));
                String line;
                StringBuilder sb = new StringBuilder();
                boolean capturing = false;
                boolean passedEndMarker = false;
                int consecutiveEmptyLines = 0;
                String upperTarget = targetAddr.toUpperCase();

                while ((line = br.readLine()) != null) {
                    if (!capturing) {
                        if (line.contains(upperTarget)) {
                            Matcher mAddr = patAddr.matcher(line);
                            if (mAddr.find() && mAddr.group(1).equalsIgnoreCase(targetAddr)) {
                                String cleanContent = line.substring(mAddr.end()).trim();
                                if (cleanContent.isEmpty() || cleanContent.equals(";") || cleanContent.contains("S U B R O U T I N E")) continue; 
                                capturing = true;
                                sb.append(line).append("\n");
                            }
                        }
                    } else {
                        if (line.contains("; =============== S U B R O U T I N E") || line.contains("proc near")) {
                            if (passedEndMarker) break; 
                        }

                        String lineContent = line;
                        Matcher mAddr = patAddr.matcher(line);
                        if (mAddr.find()) lineContent = line.substring(mAddr.end()).trim();
                        else lineContent = lineContent.trim();

                        if (lineContent.isEmpty() || lineContent.equals(";")) consecutiveEmptyLines++;
                        else consecutiveEmptyLines = 0;

                        if (passedEndMarker && consecutiveEmptyLines >= 2) break;

                        sb.append(line).append("\n");

                        if (line.contains("; End of function") || line.contains("endp")) passedEndMarker = true;
                        if (passedEndMarker && line.contains("; } // starts at")) break; 
                        if (passedEndMarker && (line.contains("Segment type:") || line.contains("Section "))) break;
                    }
                }
                br.close();

                String tempRes = sb.toString().trim();
                tempRes = tempRes.replaceAll("(\\n\\s*[a-zA-Z0-9_\\.\\-]+:[0-9A-Fa-f]+\\s*)+$", "");
                final String res = tempRes;

                new Handler(Looper.getMainLooper()).post(() -> {
                    pd.dismiss();
                    if (res.isEmpty()) {
                        Toast.makeText(MainActivity.this, "Failed to copy: Address not found.", Toast.LENGTH_SHORT).show();
                    } else {
                        android.content.ClipboardManager clipboard = (android.content.ClipboardManager) getSystemService(Context.CLIPBOARD_SERVICE);
                        android.content.ClipData clip = android.content.ClipData.newPlainText("IDA Function", res);
                        clipboard.setPrimaryClip(clip);
                        Toast.makeText(MainActivity.this, "Function copied to clipboard!", Toast.LENGTH_SHORT).show();
                    }
                });
            } catch (Exception e) {
                new Handler(Looper.getMainLooper()).post(() -> {
                    pd.dismiss();
                    Toast.makeText(MainActivity.this, "Error: " + e.getMessage(), Toast.LENGTH_SHORT).show();
                });
            }
        }).start();
    }

    private long parseHexAddress(String hex) {
        long result = 0;
        for (int i = 0; i < hex.length(); i++) {
            char c = hex.charAt(i);
            int val = -1;
            if (c >= '0' && c <= '9') val = c - '0';
            else if (c >= 'A' && c <= 'F') val = c - 'A' + 10;
            else if (c >= 'a' && c <= 'f') val = c - 'a' + 10;
            if (val != -1) result = (result << 4) | val;
        }
        return result;
    }

    private List<Xref> getXrefs(String addrHex, boolean isTo) {
        List<Xref> result = new ArrayList<>();
        RandomAccessFile raf = null;
        try {
            long addr = parseHexAddress(addrHex);
            LongArray offsets = isTo ? xrefsToOffsets.get(addr) : xrefsFromOffsets.get(addr);
            if (offsets == null || offsets.size == 0) return result;

            raf = new RandomAccessFile(new File(getCacheDir(), "xrefs.txt"), "r");
            for (int i = 0; i < offsets.size; i++) {
                raf.seek(offsets.get(i));
                String line = raf.readLine();
                if (line != null) {
                    // readLine в RAF читает в ISO-8859-1, конвертируем обратно в UTF-8 для корректных имен
                    String utf8Line = new String(line.getBytes("ISO-8859-1"), "UTF-8");
                    String[] p = utf8Line.split("\t");
                    if (p.length >= 5) result.add(new Xref(p[0], p[1], p[2], p[3], p[4]));
                }
            }
        } catch (Exception e) {
            e.printStackTrace();
        } finally {
            if (raf != null) try { raf.close(); } catch (Exception e) {}
        }
        return result;
    }

    private void showXrefsList(String addr, boolean isTo) {
        List<Xref> refs = getXrefs(addr, isTo);
        if (refs.isEmpty()) {
            Toast.makeText(this, "No xrefs " + (isTo ? "to" : "from") + " this address.", Toast.LENGTH_SHORT).show();
            return;
        }
        AlertDialog.Builder b = new AlertDialog.Builder(this);
        b.setTitle("Xrefs " + (isTo ? "to " : "from ") + addr);
        ListView lv = new ListView(this);
        
        List<String> displayList = new ArrayList<>();
        for (Xref x : refs) {
            String dir = x.type.equals("C") ? "Code" : "Data";
            if (isTo) displayList.add("[" + dir + "] " + x.fromName + "  (" + x.fromAddr + ")");
            else displayList.add("[" + dir + "] " + x.toName + "  (" + x.toAddr + ")");
        }
        
        lv.setAdapter(new BaseAdapter() {
            @Override public int getCount() { return displayList.size(); }
            @Override public Object getItem(int pos) { return null; }
            @Override public long getItemId(int pos) { return pos; }
            @Override public View getView(int pos, View cv, ViewGroup p) {
                TextView tv = new TextView(MainActivity.this);
                tv.setText(displayList.get(pos));
                tv.setPadding(30, 30, 30, 30);
                tv.setTextSize(14);
                return tv;
            }
        });
        
        Dialog dialog = b.setView(lv).setNegativeButton("Close", null).create();
        lv.setOnItemClickListener((parent, view, position, id) -> {
            dialog.dismiss();
            jumpToAddress(isTo ? refs.get(position).fromAddr : refs.get(position).toAddr);
        });
        dialog.show();
    }

    private void showXrefsGraph(String addr, boolean isTo) {
        Dialog d = new Dialog(this, android.R.style.Theme_Black_NoTitleBar_Fullscreen);
        XrefGraphView graphView = new XrefGraphView(this, addr, isTo, d);
        d.setContentView(graphView);
        d.show();
    }

    private void showCommentDialog(final String addr) {
        AlertDialog.Builder b = new AlertDialog.Builder(this);
        b.setTitle("Enter comment");
        final EditText input = new EditText(this);
        if (pendingComments.containsKey(addr)) input.setText(pendingComments.get(addr));
        b.setView(input);
        b.setPositiveButton("OK", (dialog, which) -> {
            String cmt = input.getText().toString();
            if (!cmt.isEmpty()) {
                pendingComments.put(addr, cmt);
                listAdapter.notifyDataSetChanged();
            }
        });
        b.setNegativeButton("Cancel", null);
        b.show();
    }

    private void showRenameDialog(final String oldName) {
        AlertDialog.Builder b = new AlertDialog.Builder(this);
        b.setTitle("Rename");
        final EditText input = new EditText(this);
        input.setText(pendingRenames.containsKey(oldName) ? pendingRenames.get(oldName) : oldName);
        b.setView(input);
        b.setPositiveButton("OK", (dialog, which) -> {
            String newName = input.getText().toString();
            if (newName.matches("^[a-zA-Z_]+$")) {
                pendingRenames.put(oldName, newName);
                listAdapter.notifyDataSetChanged();
            } else {
                Toast.makeText(this, "Invalid name! Only Latin letters and underscores allowed.", Toast.LENGTH_SHORT).show();
            }
        });
        b.setNegativeButton("Cancel", null);
        b.show();
    }

    private String applyPendingChanges(String chunkText) {
        if (pendingComments.isEmpty() && pendingRenames.isEmpty()) return chunkText;
        StringBuilder sb = new StringBuilder();
        String[] lines = chunkText.split("\n", -1);
        for (int i = 0; i < lines.length; i++) {
            String line = lines[i];
            if (i == lines.length - 1 && line.isEmpty()) continue; 
            for (Map.Entry<String, String> entry : pendingRenames.entrySet()) {
                line = line.replaceAll("(?<![a-zA-Z0-9_])" + entry.getKey() + "(?![a-zA-Z0-9_])", entry.getValue());
            }
            if (!pendingComments.isEmpty()) {
                Matcher mAddr = patAddr.matcher(line);
                if (mAddr.find()) {
                    String addr = mAddr.group(1);
                    if (pendingComments.containsKey(addr)) line = line + " ; " + pendingComments.get(addr);
                }
            }
            sb.append(line).append("\n");
        }
        return sb.toString();
    }

    // --- Кастомный View для WinGraph32-стайл графов ---
    private class XrefGraphView extends View {
        private Paint nodePaint, textPaint, edgeCodePaint, edgeDataPaint, bgPaint;
        private List<GraphNode> nodes = new ArrayList<>();
        private List<GraphEdge> edges = new ArrayList<>();
        
        private float scale = 1.0f;
        private float dx = 0f, dy = 0f;
        private ScaleGestureDetector scaleDetector;
        private GestureDetector dragDetector;
        private Dialog parentDialog;

        class GraphNode {
            String addr, name;
            RectF rect;
            int depth, xIndex;
            GraphNode(String a, String n, int d, int xI) { addr=a; name=n; depth=d; xIndex=xI; }
        }
        class GraphEdge {
            GraphNode from, to; boolean isCode;
            GraphEdge(GraphNode f, GraphNode t, boolean c) { from=f; to=t; isCode=c; }
        }

        public XrefGraphView(Context context, String rootAddr, boolean isToGraph, Dialog d) {
            super(context);
            this.parentDialog = d;
            bgPaint = new Paint(); bgPaint.setColor(Color.parseColor("#F0F0F0"));
            nodePaint = new Paint(); nodePaint.setColor(Color.parseColor("#FFFFCC")); nodePaint.setStyle(Paint.Style.FILL_AND_STROKE); nodePaint.setStrokeWidth(2);
            textPaint = new Paint(); textPaint.setColor(Color.BLACK); textPaint.setTextSize(30); textPaint.setTypeface(Typeface.MONOSPACE);
            edgeCodePaint = new Paint(); edgeCodePaint.setColor(Color.BLUE); edgeCodePaint.setStrokeWidth(4); edgeCodePaint.setStyle(Paint.Style.STROKE);
            edgeDataPaint = new Paint(); edgeDataPaint.setColor(Color.parseColor("#008000")); edgeDataPaint.setStrokeWidth(4); edgeDataPaint.setStyle(Paint.Style.STROKE);

            buildGraph(rootAddr, isToGraph);

            scaleDetector = new ScaleGestureDetector(context, new ScaleGestureDetector.SimpleOnScaleGestureListener() {
                @Override public boolean onScale(ScaleGestureDetector det) {
                    scale *= det.getScaleFactor();
                    scale = Math.max(0.1f, Math.min(scale, 5.0f));
                    invalidate(); return true;
                }
            });

            dragDetector = new GestureDetector(context, new GestureDetector.SimpleOnGestureListener() {
                @Override public boolean onScroll(MotionEvent e1, MotionEvent e2, float distanceX, float distanceY) {
                    dx -= distanceX / scale; dy -= distanceY / scale;
                    invalidate(); return true;
                }
                @Override public boolean onSingleTapConfirmed(MotionEvent e) {
                    float touchX = (e.getX() - getWidth()/2f) / scale + getWidth()/2f - dx;
                    float touchY = (e.getY() - getHeight()/2f) / scale + getHeight()/2f - dy;
                    for (GraphNode n : nodes) {
                        if (n.rect != null && n.rect.contains(touchX, touchY)) {
                            if (parentDialog != null) parentDialog.dismiss();
                            jumpToAddress(n.addr);
                            return true;
                        }
                    }
                    return false;
                }
            });
        }

        private void buildGraph(String rootAddr, boolean isToGraph) {
            Map<String, GraphNode> built = new HashMap<>();
            List<GraphNode> currentLevel = new ArrayList<>();
            GraphNode root = new GraphNode(rootAddr, "Root", 0, 0);
            built.put(rootAddr, root); currentLevel.add(root); nodes.add(root);

            int depth = 1;
            while(!currentLevel.isEmpty() && depth < 10) { // Ограничим глубину во избежание зависаний
                List<GraphNode> nextLevel = new ArrayList<>();
                int xIdx = 0;
                for (GraphNode n : currentLevel) {
                    List<Xref> links = getXrefs(n.addr, isToGraph);
                    if (links != null && !links.isEmpty()) {
                        for (Xref link : links) {
                            String targetAddr = isToGraph ? link.fromAddr : link.toAddr;
                            String targetName = isToGraph ? link.fromName : link.toName;
                            
                            GraphNode child = built.get(targetAddr);
                            if (child == null) {
                                child = new GraphNode(targetAddr, targetName, depth, xIdx++);
                                built.put(targetAddr, child);
                                nextLevel.add(child);
                                nodes.add(child);
                            }
                            edges.add(new GraphEdge(isToGraph ? child : n, isToGraph ? n : child, link.type.equals("C")));
                        }
                    }
                }
                currentLevel = nextLevel;
                depth++;
            }
            layoutNodes();
        }

        private void layoutNodes() {
            int nodeWidth = 400; int nodeHeight = 100;
            int xSpacing = 50; int ySpacing = 150;

            Map<Integer, Integer> levelCount = new HashMap<>();
            for (GraphNode n : nodes) {
                levelCount.put(n.depth, Math.max(levelCount.getOrDefault(n.depth, 0), n.xIndex + 1));
            }

            for (GraphNode n : nodes) {
                int countAtLevel = levelCount.get(n.depth);
                int totalWidth = countAtLevel * nodeWidth + (countAtLevel - 1) * xSpacing;
                int startX = (getResources().getDisplayMetrics().widthPixels - totalWidth) / 2;
                
                float left = startX + n.xIndex * (nodeWidth + xSpacing);
                float top = 100 + n.depth * (nodeHeight + ySpacing);
                n.rect = new RectF(left, top, left + nodeWidth, top + nodeHeight);
            }
        }

        @Override public boolean onTouchEvent(MotionEvent event) {
            scaleDetector.onTouchEvent(event);
            dragDetector.onTouchEvent(event);
            return true;
        }

        @Override protected void onDraw(Canvas canvas) {
            canvas.drawColor(bgPaint.getColor());
            canvas.save();
            canvas.scale(scale, scale, getWidth()/2f, getHeight()/2f);
            canvas.translate(dx, dy);

            // Draw edges
            for (GraphEdge e : edges) {
                Paint p = e.isCode ? edgeCodePaint : edgeDataPaint;
                float startX = e.from.rect.centerX(); float startY = e.from.rect.bottom;
                float stopX = e.to.rect.centerX(); float stopY = e.to.rect.top;
                
                Path path = new Path();
                path.moveTo(startX, startY);
                // Simple orthogonal routing
                path.lineTo(startX, startY + (stopY - startY) / 2);
                path.lineTo(stopX, startY + (stopY - startY) / 2);
                path.lineTo(stopX, stopY);
                canvas.drawPath(path, p);
                
                // Draw Arrowhead
                canvas.drawLine(stopX, stopY, stopX - 10, stopY - 15, p);
                canvas.drawLine(stopX, stopY, stopX + 10, stopY - 15, p);
            }

            // Draw nodes (IDA Authentic style)
            for (GraphNode n : nodes) {
                nodePaint.setColor(Color.BLACK);
                canvas.drawRect(n.rect.left-2, n.rect.top-2, n.rect.right+2, n.rect.bottom+2, nodePaint);
                nodePaint.setColor(Color.parseColor("#FFFFCC"));
                canvas.drawRect(n.rect, nodePaint);
                canvas.drawText(n.addr, n.rect.left + 10, n.rect.top + 35, textPaint);
                canvas.drawText(n.name, n.rect.left + 10, n.rect.top + 75, textPaint);
            }
            canvas.restore();
        }
    }

    private class IdaAdapter extends BaseAdapter {
        @Override public int getCount() {
            LongArray offsets;
            if (currentTab == 0) offsets = idaOffsets;
            else if (currentTab == 1) offsets = hexOffsets;
            else if (currentTab == 2) offsets = isSearchingStrings ? filteredStrOffsets : strOffsets;
            else offsets = isSearchingStrings ? filteredFuncOffsets : funcOffsets;
            return Math.max(0, offsets.size - 1);
        }
        @Override public Object getItem(int position) { return null; }
        @Override public long getItemId(int position) { return position; }

        @Override public View getView(int position, View convertView, ViewGroup parent) {
            final TextView tv;
            if (convertView == null) {
                tv = new TextView(MainActivity.this);
                tv.setTextColor(Color.BLACK); tv.setTextSize(12);
                tv.setTypeface(Typeface.MONOSPACE); tv.setPadding(16, 0, 16, 0); 
                tv.setIncludeFontPadding(false); // Убирает вертикальные пустоты шрифта
                tv.setLineSpacing(0, 1.0f);
                tv.setFocusable(true); tv.setFocusableInTouchMode(true);
                
                final GestureDetector gd = new GestureDetector(MainActivity.this, new GestureDetector.SimpleOnGestureListener() {
                    @Override public boolean onSingleTapConfirmed(MotionEvent e) {
                        if (currentTab != 0 && !highlightedAddress.isEmpty()) {
                            selectedStrAddress = highlightedAddress;
                            Layout layout = tv.getLayout();
                            if (layout != null) {
                                int x = (int) e.getX() - tv.getTotalPaddingLeft() + tv.getScrollX();
                                int line = layout.getLineForVertical((int) e.getY() - tv.getTotalPaddingTop() + tv.getScrollY());
                                int offset = layout.getOffsetForHorizontal(line, x);
                                int lineStart = layout.getLineStart(line);
                                int charPos = offset - lineStart;
                                if (currentTab == 2) { // Strings
                                    if (charPos <= 21) selectedColumnIndex = 0;
                                    else if (charPos <= 32) selectedColumnIndex = 1;
                                    else if (charPos <= 37) selectedColumnIndex = 2;
                                    else selectedColumnIndex = 3;
                                } else if (currentTab == 3) { // Functions
                                    if (charPos <= 21) selectedColumnIndex = 0;
                                    else if (charPos <= 32) selectedColumnIndex = 1;
                                    else selectedColumnIndex = 2;
                                } else if (currentTab == 1) { // Hex View
                                    if (charPos <= 10) selectedColumnIndex = 0;
                                    else if (charPos <= 59) selectedColumnIndex = 1;
                                    else selectedColumnIndex = 2;
                                }
                            }
                            listView.invalidateViews();
                            return true;
                        }
                        return false;
                    }

                    @Override public boolean onDoubleTap(MotionEvent e) {
                        if (currentTab != 0 && !highlightedAddress.isEmpty()) { jumpToAddress(highlightedAddress); return true; }
                        return false;
                    }
                    
                    @Override public void onLongPress(MotionEvent e) {
                        if (currentTab == 0) {
                            int x = (int) e.getX() - tv.getTotalPaddingLeft() + tv.getScrollX();
                            int y = (int) e.getY() - tv.getTotalPaddingTop() + tv.getScrollY();
                            Layout layout = tv.getLayout();
                            if (layout != null) {
                                int line = layout.getLineForVertical(Math.max(0, y));
                                if (line >= 0 && line < layout.getLineCount()) {
                                    int start = layout.getLineStart(line);
                                    int end = layout.getLineEnd(line);
                                    CharSequence lineStr = tv.getText().subSequence(start, end);
                                    
                                    String addr = "";
                                    Matcher mAddr = patAddr.matcher(lineStr);
                                    if (mAddr.find()) addr = mAddr.group(1);
                                    
                                    int offset = layout.getOffsetForHorizontal(line, x);
                                    String word = extractWord(lineStr.toString(), offset - start);
                                    showLongTapMenu(addr, word);
                                }
                            }
                        } else if (currentTab == 1) {
                            int y = (int) e.getY() - tv.getTotalPaddingTop() + tv.getScrollY();
                            Layout layout = tv.getLayout();
                            if (layout != null) {
                                int line = layout.getLineForVertical(Math.max(0, y));
                                if (line >= 0 && line < layout.getLineCount()) {
                                    int start = layout.getLineStart(line);
                                    int end = layout.getLineEnd(line);
                                    String lineStr = tv.getText().subSequence(start, end).toString();
                                    
                                    Matcher m = Pattern.compile("^[0-9A-Fa-f]+\\s+((?:[0-9A-Fa-f]{2}\\s*)+)").matcher(lineStr.trim());
                                    if (m.find()) {
                                        String rawHex = m.group(1).replace(" ", "");
                                        ClipboardManager clipboard = (ClipboardManager) getSystemService(Context.CLIPBOARD_SERVICE);
                                        ClipData clip = ClipData.newPlainText("IDA Hex", rawHex);
                                        clipboard.setPrimaryClip(clip);
                                        Toast.makeText(MainActivity.this, "Copied Hex (no spaces):\n" + rawHex, Toast.LENGTH_SHORT).show();
                                    }
                                }
                            }
                        }
                    }
                });

                tv.setOnTouchListener((v, event) -> {
                    gd.onTouchEvent(event);
                    int action = event.getActionMasked();
                    if (action == MotionEvent.ACTION_DOWN || action == MotionEvent.ACTION_HOVER_MOVE) {
                        int x = (int) event.getX() - tv.getTotalPaddingLeft() + tv.getScrollX();
                        int y = (int) event.getY() - tv.getTotalPaddingTop() + tv.getScrollY();
                        Layout layout = tv.getLayout();
                        if (layout != null) {
                            int line = layout.getLineForVertical(Math.max(0, y));
                            if (line >= 0 && line < layout.getLineCount()) {
                                int start = layout.getLineStart(line);
                                CharSequence lineStr = tv.getText().subSequence(start, layout.getLineEnd(line));
                                Matcher m = patAddr.matcher(lineStr);
                                if (m.find()) {
                                    String addr = m.group(1);
                                    if (!addr.equals(highlightedAddress)) { highlightedAddress = addr; if (currentTab == 0) listView.invalidateViews(); }
                                } else {
                                    String[] tokens = lineStr.toString().trim().split("\\s+");
                                    String firstToken = tokens.length > 0 ? tokens[0].trim() : "";
                                    int colonIdx = firstToken.indexOf(':');
                                    highlightedAddress = (colonIdx >= 0) ? firstToken.substring(colonIdx + 1) : firstToken;
                                }
                            }
                        }
                    }
                    return false; 
                });
            } else { tv = (TextView) convertView; tv.setTextIsSelectable(false); tv.clearFocus(); }

            File targetFile; LongArray offsets;
            if (currentTab == 0) { targetFile = cacheIdaFile; offsets = idaOffsets; }
            else if (currentTab == 1) { targetFile = cacheHexFile; offsets = hexOffsets; }
            else if (currentTab == 2) { targetFile = isSearchingStrings ? cacheFilteredStrFile : cacheStrFile; offsets = isSearchingStrings ? filteredStrOffsets : strOffsets; }
            else { targetFile = isSearchingStrings ? cacheFilteredFuncFile : cacheFuncFile; offsets = isSearchingStrings ? filteredFuncOffsets : funcOffsets; }

            try {
                RandomAccessFile raf = new RandomAccessFile(targetFile, "r");
                long startByte = offsets.get(position);
                int length = (int) (offsets.get(position + 1) - startByte);
                if (length > 0) {
                    byte[] buffer = new byte[length];
                    raf.seek(startByte); raf.readFully(buffer);
                    String chunkText = new String(buffer, "UTF-8");
                    if (chunkText.endsWith("\n")) chunkText = chunkText.substring(0, chunkText.length() - 1); 
                    
                    if (currentTab == 0) {
                        chunkText = applyPendingChanges(chunkText);
                        if (isShowHexEnabled) {
                            StringBuilder sb = new StringBuilder();
                            long lastSeenAddr = -1;
                            long currentHexPtr = -1;
                            RandomAccessFile hexRaf = null;
                            long hexFileLength = 0;
                            try { 
                                hexRaf = new RandomAccessFile(cacheItemHexFile, "r"); 
                                hexFileLength = hexRaf.length();
                            } catch(Exception e){}
                            
                            for (String line : chunkText.split("\n", -1)) {
                                long currentLineAddr = -1;
                                Matcher mAddr = patAddr.matcher(line);
                                if (mAddr.find()) {
                                    try { currentLineAddr = Long.parseLong(mAddr.group(1), 16); } catch(Exception e){}
                                }
                                String hexToAppend = null;
                                if (currentLineAddr != -1 && currentLineAddr != lastSeenAddr && hexRaf != null && hexFileLength > 0) {
                                    lastSeenAddr = currentLineAddr;
                                    boolean found = false;

                                    // БЫСТРЫЙ ПУТЬ: Последовательное чтение (работает для 99% строк, так как мы идем вниз по чанку)
                                    if (currentHexPtr != -1) {
                                        try {
                                            hexRaf.seek(currentHexPtr);
                                            for (int i = 0; i < 5; i++) { // Проверяем до 5 строк вперед
                                                long ptrBefore = hexRaf.getFilePointer();
                                                String hLine = hexRaf.readLine();
                                                if (hLine == null) break;
                                                
                                                int tabIdx = hLine.indexOf('\t');
                                                if (tabIdx > 0) {
                                                    long hAddr = Long.parseLong(hLine.substring(0, tabIdx).trim(), 16);
                                                    if (hAddr == currentLineAddr) {
                                                        hexToAppend = hLine.substring(tabIdx + 1).trim();
                                                        currentHexPtr = hexRaf.getFilePointer(); // Запоминаем для следующей строки
                                                        found = true;
                                                        break;
                                                    } else if (hAddr > currentLineAddr) {
                                                        currentHexPtr = ptrBefore; // Промах, откатываемся, чтобы следующая строка проверила отсюда
                                                        break;
                                                    }
                                                }
                                            }
                                        } catch (Exception e) {}
                                    }

                                    // МЕДЛЕННЫЙ ПУТЬ: Прямой бинарный поиск по файлу без бесконечного цикла (вызывается 1 раз на чанк)
                                    if (!found) {
                                        long low = 0;
                                        long high = hexFileLength;
                                        try {
                                            while (low <= high) {
                                                long mid = (low + high) >>> 1;
                                                hexRaf.seek(mid);
                                                
                                                if (mid > 0) {
                                                    while (mid < high && hexRaf.read() != '\n') mid++;
                                                }
                                                
                                                long lineStart = hexRaf.getFilePointer();
                                                String hLine = hexRaf.readLine();
                                                long nextLineStart = hexRaf.getFilePointer(); // БЕЗОПАСНЫЙ сдвиг low (защита от бесконечного цикла)
                                                
                                                if (hLine == null) {
                                                    high = mid - 1;
                                                    continue;
                                                }
                                                
                                                int tabIdx = hLine.indexOf('\t');
                                                if (tabIdx > 0) {
                                                    long hAddr = Long.parseLong(hLine.substring(0, tabIdx).trim(), 16);
                                                    if (hAddr == currentLineAddr) {
                                                        hexToAppend = hLine.substring(tabIdx + 1).trim();
                                                        currentHexPtr = nextLineStart;
                                                        break;
                                                    } else if (hAddr < currentLineAddr) {
                                                        low = nextLineStart;
                                                        if (low <= lineStart) low = lineStart + 1; // Запасной парашют от зависания
                                                    } else {
                                                        high = mid - 1;
                                                    }
                                                } else {
                                                    low = nextLineStart;
                                                    if (low <= lineStart) low = lineStart + 1;
                                                }
                                            }
                                        } catch (Exception e) {}
                                    }
                                }
                                
                                if (hexToAppend != null && !hexToAppend.isEmpty()) {
                                    int cmtIdx = line.indexOf(';');
                                    if (cmtIdx >= 0) {
                                        sb.append(line.substring(0, cmtIdx)).append("( ").append(hexToAppend).append(" ) ").append(line.substring(cmtIdx)).append("\n");
                                    } else {
                                        sb.append(line).append(" ( ").append(hexToAppend).append(" )\n");
                                    }
                                } else {
                                    sb.append(line).append("\n");
                                }
                            }
                            if (hexRaf != null) { try { hexRaf.close(); } catch(Exception e){} }
                            if (sb.length() > 0) sb.setLength(sb.length() - 1);
                            chunkText = sb.toString();
                        }
                        tv.setText(applyIdaStyle(chunkText));
                    }
                    else if (currentTab == 1) tv.setText(formatHexTab(chunkText));
                    else if (currentTab == 2) tv.setText(formatStringsTab(chunkText));
                    else tv.setText(formatFunctionsTab(chunkText));
                }
                raf.close();
            } catch (Exception e) { tv.setText("Error reading chunk."); }

            tv.setTextIsSelectable(true);
            return tv;
        }
    }

    private CharSequence formatHexTab(String text) {
        String[] lines = text.split("\n");
        SpannableStringBuilder ssb = new SpannableStringBuilder();
        for (String line : lines) {
            String[] parts = line.split("\t");
            if (parts.length >= 3) {
                int c0Start = ssb.length(); String c0 = String.format("%-10s", parts[0]);
                int c1Start = c0Start + c0.length(); String c1 = String.format("%-48s", parts[1]); // 16 bytes * 3 = 48
                int c2Start = c1Start + c1.length(); String c2 = parts[2];
                ssb.append(String.format("%s %s %s\n", c0, c1, c2));
                
                if (currentTab == 1 && parts[0].equals(selectedStrAddress) && selectedColumnIndex != -1) {
                    int hStart = -1, hEnd = -1;
                    if (selectedColumnIndex == 0) { hStart = c0Start; hEnd = c0Start + c0.length() - 1; }
                    else if (selectedColumnIndex == 1) { hStart = c1Start; hEnd = c1Start + c1.length() - 1; }
                    else if (selectedColumnIndex == 2) { hStart = c2Start; hEnd = c2Start + c2.length(); }
                    if (hStart != -1) ssb.setSpan(new BackgroundColorSpan(Color.parseColor("#B4D5FE")), hStart, hEnd, Spannable.SPAN_EXCLUSIVE_EXCLUSIVE);
                }
            } else ssb.append(line).append("\n");
        }
        
        Matcher mAddr = Pattern.compile("^[0-9A-Fa-f]{8,}").matcher(ssb);
        while (mAddr.find()) ssb.setSpan(new ForegroundColorSpan(Color.GRAY), mAddr.start(), mAddr.end(), 33);
        Matcher mHex = Pattern.compile("(?<=^.{11})([0-9A-Fa-f]{2} )+").matcher(ssb);
        while (mHex.find()) ssb.setSpan(new ForegroundColorSpan(Color.parseColor("#000080")), mHex.start(), mHex.end(), 33);
        
        return ssb;
    }

    private CharSequence formatStringsTab(String text) {
        String[] lines = text.split("\n");
        SpannableStringBuilder ssb = new SpannableStringBuilder();
        for (String line : lines) {
            String[] parts = line.split("\t");
            if (parts.length >= 4) {
                int sOL = ssb.length(); ssb.append(" "); ssb.setSpan(new QuoteBadgeSpan(), sOL, sOL + 1, Spannable.SPAN_EXCLUSIVE_EXCLUSIVE);
                int c0Start = ssb.length() + 1; String c0 = String.format("%-18s", parts[0]);
                int c1Start = c0Start + c0.length() + 1; String c1 = String.format("%-10s", parts[1]);
                int c2Start = c1Start + c1.length() + 1; String c2 = String.format("%-4s", parts[2]);
                int c3Start = c2Start + c2.length() + 1; String c3 = parts[3];
                ssb.append(String.format(" %s %s %s %s\n", c0, c1, c2, c3));
                
                if (currentTab == 2 && parts[0].equals(selectedStrAddress) && selectedColumnIndex != -1) {
                    int hStart = -1, hEnd = -1;
                    if (selectedColumnIndex == 0) { hStart = c0Start; hEnd = c0Start + c0.length(); }
                    else if (selectedColumnIndex == 1) { hStart = c1Start; hEnd = c1Start + c1.length(); }
                    else if (selectedColumnIndex == 2) { hStart = c2Start; hEnd = c2Start + c2.length(); }
                    else if (selectedColumnIndex == 3) { hStart = c3Start; hEnd = c3Start + c3.length(); }
                    if (hStart != -1) ssb.setSpan(new BackgroundColorSpan(Color.parseColor("#B4D5FE")), hStart, hEnd, Spannable.SPAN_EXCLUSIVE_EXCLUSIVE);
                }
            } else ssb.append(line).append("\n");
        }
        return ssb;
    }

    private CharSequence formatFunctionsTab(String text) {
        String[] lines = text.split("\n");
        SpannableStringBuilder ssb = new SpannableStringBuilder();
        for (String line : lines) {
            String[] parts = line.split("\t");
            if (parts.length >= 3) {
                int c0Start = ssb.length(); String c0 = String.format("%-20s", parts[0]);
                int c1Start = c0Start + c0.length(); String c1 = String.format("%-10s", parts[1]);
                int c2Start = c1Start + c1.length(); String c2 = parts[2];
                ssb.append(String.format("%s%s%s\n", c0, c1, c2));
                
                if (currentTab == 3 && parts[0].equals(selectedStrAddress) && selectedColumnIndex != -1) {
                    int hStart = -1, hEnd = -1;
                    if (selectedColumnIndex == 0) { hStart = c0Start; hEnd = c0Start + c0.length() - 1; }
                    else if (selectedColumnIndex == 1) { hStart = c1Start; hEnd = c1Start + c1.length() - 1; }
                    else if (selectedColumnIndex == 2) { hStart = c2Start; hEnd = c2Start + c2.length(); }
                    if (hStart != -1) ssb.setSpan(new BackgroundColorSpan(Color.parseColor("#B4D5FE")), hStart, hEnd, Spannable.SPAN_EXCLUSIVE_EXCLUSIVE);
                }
            } else ssb.append(line).append("\n");
        }
        return ssb;
    }

    private SpannableStringBuilder applyIdaStyle(String text) {
        text = text.replace("\r", "");
        SpannableStringBuilder ssb = new SpannableStringBuilder(text);
        int offset = 0;
        int baseBlueColor = Color.BLUE, navyColor = Color.parseColor("#000080");
        int greenColor = Color.parseColor("#008000"), lightBlueXref = Color.parseColor("#8080FF");

        for (String line : text.split("\n")) {
            int lineLen = line.length(), commentIdx = line.indexOf(';');
            String code = line.substring(0, commentIdx >= 0 ? commentIdx : lineLen);

            Matcher mBlue = patBlueBase.matcher(code); while (mBlue.find()) ssb.setSpan(new ForegroundColorSpan(baseBlueColor), offset + mBlue.start(), offset + mBlue.end(), 33);
            if (!patDirectives.matcher(code).find()) {
                Matcher mNavy = patNavyKey.matcher(code); while (mNavy.find()) ssb.setSpan(new ForegroundColorSpan(navyColor), offset + mNavy.start(), offset + mNavy.end(), 33);
                Matcher mReg = patNavyReg.matcher(code); while (mReg.find()) ssb.setSpan(new ForegroundColorSpan(navyColor), offset + mReg.start(), offset + mReg.end(), 33);
                Matcher mPunct = patNavyPunct.matcher(code); while (mPunct.find()) ssb.setSpan(new ForegroundColorSpan(navyColor), offset + mPunct.start(), offset + mPunct.end(), 33);
            }
            Matcher mLabels = patNavyLabels.matcher(code); while (mLabels.find()) ssb.setSpan(new ForegroundColorSpan(navyColor), offset + mLabels.start(), offset + mLabels.end(), 33);
            Matcher mOff = patNavyOffsetArg.matcher(code); while (mOff.find()) ssb.setSpan(new ForegroundColorSpan(navyColor), offset + mOff.start(1), offset + mOff.end(1), 33);
            Matcher mDef = patNavyDataDef.matcher(code); while (mDef.find()) ssb.setSpan(new ForegroundColorSpan(navyColor), offset + mDef.start(1), offset + mDef.end(1), 33);
            Matcher mVar = patGreenVar.matcher(code); while (mVar.find()) ssb.setSpan(new ForegroundColorSpan(greenColor), offset + mVar.start(), offset + mVar.end(), 33);
            Matcher mNum = patGreenNum.matcher(code); while (mNum.find()) ssb.setSpan(new ForegroundColorSpan(greenColor), offset + mNum.start(), offset + mNum.end(), 33);
            Matcher mStr = patStr.matcher(code);
            while (mStr.find()) {
                if (mStr.group().equals("'CODE'") || mStr.group().equals("'DATA'")) ssb.setSpan(new ForegroundColorSpan(baseBlueColor), offset + mStr.start(), offset + mStr.end(), 33);
                else {
                    ssb.setSpan(new ForegroundColorSpan(navyColor), offset + mStr.start(), offset + mStr.start() + 1, 33);
                    ssb.setSpan(new ForegroundColorSpan(navyColor), offset + mStr.end() - 1, offset + mStr.end(), 33);
                    if (mStr.end() - mStr.start() > 2) ssb.setSpan(new ForegroundColorSpan(greenColor), offset + mStr.start() + 1, offset + mStr.end() - 1, 33);
                }
            }
            Matcher mPink = patPink.matcher(code); while (mPink.find()) ssb.setSpan(new ForegroundColorSpan(Color.parseColor("#FF00FF")), offset + mPink.start(1), offset + mPink.end(1), 33);
            Matcher mAddr = patAddr.matcher(code); if (mAddr.find()) ssb.setSpan(new DynamicAddressSpan(mAddr.group(1)), offset + mAddr.start(), offset + mAddr.end(), 33);

            Matcher mHexIn = Pattern.compile("\\(\\s([0-9A-Fa-f]{2}\\s)+\\)").matcher(code);
            while (mHexIn.find()) ssb.setSpan(new ForegroundColorSpan(Color.parseColor("#8B008B")), offset + mHexIn.start(), offset + mHexIn.end(), 33);

            if (commentIdx >= 0) {
                String cmt = line.substring(commentIdx);
                if (cmt.contains("DATA XREF:")) ssb.setSpan(new ForegroundColorSpan(lightBlueXref), offset + commentIdx, offset + lineLen, 33);
                else if (cmt.contains("CODE XREF:") || cmt.contains("XREF:")) ssb.setSpan(new ForegroundColorSpan(greenColor), offset + commentIdx, offset + lineLen, 33);
                else if (cmt.matches("^;\\s*={3,}.*") || cmt.matches("^;\\s*-{3,}.*") || cmt.contains("Input ") || cmt.contains("Compiler") || cmt.contains("Attributes:") || cmt.contains("Segment ") || cmt.contains("const ") || cmt.contains("org ") || cmt.matches("^;\\s*_[a-zA-Z0-9_]+$") || cmt.matches("^;\\s*[0-9A-Fa-f]+h?$") || cmt.contains("\"") || cmt.contains("'")) ssb.setSpan(new ForegroundColorSpan(Color.GRAY), offset + commentIdx, offset + lineLen, 33);
                else ssb.setSpan(new ForegroundColorSpan(baseBlueColor), offset + commentIdx, offset + lineLen, 33);
            }
            offset += lineLen + 1;
        }
        return ssb;
    }

    private class DynamicAddressSpan extends CharacterStyle implements UpdateAppearance {
        String address; public DynamicAddressSpan(String address) { this.address = address; }
        @Override public void updateDrawState(TextPaint tp) { tp.setColor(address.equals(highlightedAddress) ? Color.BLUE : Color.GRAY); }
    }

    private class QuoteBadgeSpan extends ReplacementSpan {
        int bgColor = Color.parseColor("#65E2AA"), borderColor = Color.parseColor("#31CCD0"), textColor = Color.BLACK;
        @Override public int getSize(Paint p, CharSequence t, int s, int e, Paint.FontMetricsInt fm) { return Math.round(p.measureText("\"\"") + 20); }
        @Override public void draw(Canvas c, CharSequence t, int s, int e, float x, int top, int y, int b, Paint p) {
            float width = getSize(p, t, s, e, null); float rT = top + 2; float rB = b - 2;
            Paint.Style oS = p.getStyle(); int oC = p.getColor();
            p.setStyle(Paint.Style.FILL); p.setColor(bgColor); c.drawRect(x + 2, rT, x + width - 2, rB, p);
            p.setStyle(Paint.Style.STROKE); p.setColor(borderColor); p.setStrokeWidth(2); c.drawRect(x + 2, rT, x + width - 2, rB, p);
            p.setStyle(Paint.Style.FILL); p.setColor(textColor); p.setFakeBoldText(true);
            c.drawText("\"\"", x + 2 + (width - 4 - p.measureText("\"\"")) / 2, y, p);
            p.setColor(oC); p.setStyle(oS); p.setFakeBoldText(false);
        }
    }
        static class LongMap {
        private static final int CHUNK_BITS = 13;
        private static final int CHUNK_SIZE = 1 << CHUNK_BITS; // 8192
        private static final int CHUNK_MASK = CHUNK_SIZE - 1;

        // Хэш-таблица (разбита на чанки)
        private long[][] keys;
        private int[][] heads;
        private int tableCapacity;
        private int keyCount;

        // Значения (добавляются чанками, НИКОГДА не пересоздаются)
        private int[][] values = new int[128][];
        private int[][] nexts = new int[128][];
        private int valCount = 0;

        public LongMap() {
            tableCapacity = CHUNK_SIZE;
            keys = new long[1][CHUNK_SIZE];
            heads = new int[1][CHUNK_SIZE];
            for (int i = 0; i < CHUNK_SIZE; i++) heads[0][i] = -1;
            keyCount = 0;
            values[0] = new int[CHUNK_SIZE];
            nexts[0] = new int[CHUNK_SIZE];
        }

        private void setHead(int idx, int val) { heads[idx >> CHUNK_BITS][idx & CHUNK_MASK] = val; }
        private int getHead(int idx) { return heads[idx >> CHUNK_BITS][idx & CHUNK_MASK]; }
        private void setKey(int idx, long val) { keys[idx >> CHUNK_BITS][idx & CHUNK_MASK] = val; }
        private long getKey(int idx) { return keys[idx >> CHUNK_BITS][idx & CHUNK_MASK]; }

        public void put(long key, long fileOffset) {
            // Фактор загрузки 0.75 (3/4)
            if (keyCount * 4 >= tableCapacity * 3) resizeTable();

            int vIdx = valCount++;
            int vChunk = vIdx >> CHUNK_BITS;
            int vOffset = vIdx & CHUNK_MASK;

            // Если не хватает указателей на чанки - расширяем только верхний массив ссылок (микро-аллокация)
            if (vChunk >= values.length) {
                int[][] newVals = new int[values.length * 2][];
                int[][] newNexts = new int[nexts.length * 2][];
                System.arraycopy(values, 0, newVals, 0, values.length);
                System.arraycopy(nexts, 0, newNexts, 0, nexts.length);
                values = newVals;
                nexts = newNexts;
            }

            // Инициализация новой страницы на 32 КБ (Android легко находит мелкие фрагменты памяти)
            if (values[vChunk] == null) {
                values[vChunk] = new int[CHUNK_SIZE];
                nexts[vChunk] = new int[CHUNK_SIZE];
            }
            
            // Безопасно режем fileOffset до 32 бит, файл не превышает 2 ГБ
            values[vChunk][vOffset] = (int) fileOffset;

            int mask = tableCapacity - 1;
            int idx = (int) ((key ^ (key >>> 32)) & mask);
            while (true) {
                int h = getHead(idx);
                if (h == -1) {
                    setKey(idx, key);
                    setHead(idx, vIdx);
                    nexts[vChunk][vOffset] = -1;
                    keyCount++;
                    return;
                }
                if (getKey(idx) == key) {
                    nexts[vChunk][vOffset] = h;
                    setHead(idx, vIdx);
                    return;
                }
                idx = (idx + 1) & mask;
            }
        }

        private void resizeTable() {
            int oldCap = tableCapacity;
            long[][] oldKeys = keys;
            int[][] oldHeads = heads;

            tableCapacity = oldCap * 2;
            int numChunks = tableCapacity >> CHUNK_BITS;
            keys = new long[numChunks][];
            heads = new int[numChunks][];
            for (int i = 0; i < numChunks; i++) {
                keys[i] = new long[CHUNK_SIZE];
                heads[i] = new int[CHUNK_SIZE];
                for (int j = 0; j < CHUNK_SIZE; j++) heads[i][j] = -1;
            }

            keyCount = 0;
            int mask = tableCapacity - 1;

            for (int i = 0; i < oldCap; i++) {
                int c = i >> CHUNK_BITS;
                int o = i & CHUNK_MASK;
                int h = oldHeads[c][o];
                if (h != -1) {
                    long k = oldKeys[c][o];
                    keyCount++;
                    int idx = (int) ((k ^ (k >>> 32)) & mask);
                    while (getHead(idx) != -1) idx = (idx + 1) & mask;
                    setKey(idx, k);
                    setHead(idx, h);
                }
            }
        }

        public LongArray get(long key) {
            int mask = tableCapacity - 1;
            int idx = (int) ((key ^ (key >>> 32)) & mask);
            while (true) {
                int h = getHead(idx);
                if (h == -1) return null;
                if (getKey(idx) == key) {
                    LongArray res = new LongArray();
                    int curr = h;
                    while (curr != -1) {
                        int cChunk = curr >> CHUNK_BITS;
                        int cOff = curr & CHUNK_MASK;
                        // Восстанавливаем long, обнуляя знак
                        res.add(values[cChunk][cOff] & 0xFFFFFFFFL); 
                        curr = nexts[cChunk][cOff];
                    }
                    return res;
                }
                idx = (idx + 1) & mask;
            }
        }

        public void clear() {
            tableCapacity = CHUNK_SIZE;
            keys = new long[1][CHUNK_SIZE];
            heads = new int[1][CHUNK_SIZE];
            for (int i = 0; i < CHUNK_SIZE; i++) heads[0][i] = -1;
            keyCount = 0;

            for (int i = 0; i < values.length; i++) {
                values[i] = null;
                nexts[i] = null;
            }
            values[0] = new int[CHUNK_SIZE];
            nexts[0] = new int[CHUNK_SIZE];
            valCount = 0;
        }
    }

    static class LongArray {
        long[] data = new long[2]; int size = 0;
        void add(long val) {
            if (size == data.length) { long[] n = new long[data.length * 2]; System.arraycopy(data, 0, n, 0, size); data = n; }
            data[size++] = val;
        }
        long get(int index) { return data[index]; }
        void clear() { size = 0; }
    }

    static class LongChunkArray {
        private static final int CHUNK_BITS = 13;
        private static final int CHUNK_SIZE = 1 << CHUNK_BITS; // 8192
        private static final int CHUNK_MASK = CHUNK_SIZE - 1;

        private long[][] chunks = new long[16][];
        public int size = 0;

        public void add(long val) {
            int c = size >> CHUNK_BITS;
            int o = size & CHUNK_MASK;
            if (c >= chunks.length) {
                long[][] n = new long[chunks.length * 2][];
                System.arraycopy(chunks, 0, n, 0, chunks.length);
                chunks = n;
            }
            if (chunks[c] == null) chunks[c] = new long[CHUNK_SIZE];
            chunks[c][o] = val;
            size++;
        }

        public long get(int index) {
            return chunks[index >> CHUNK_BITS][index & CHUNK_MASK];
        }

        public void clear() {
            for (int i = 0; i < chunks.length; i++) chunks[i] = null;
            size = 0;
        }
    }
}
