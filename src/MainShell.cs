// ════════════════════════════════════════════════════════════════
//  MainShell.cs  –  탭 기반 메인 셸 폼
//  탭 1 : Plasma Fingerprint 분석
//  탭 2 : 측정 데이터 뷰어 (15컬럼)
//  탭 3 : RF 임피던스 매칭 계산기
//  ※ 좌측 TreeView 네비게이션 (SplitContainer 제거 → 단순 Dock 방식 + 올바른 추가 순서로 재구성)
//  ※ 로딩 오버레이: 별도 스레드(LoadingOverlayForm)에서 실행되어
//     메인 스레드의 차트 렌더링 시간과 무관하게 Marquee 애니메이션이 끊기지 않음
//  ※ 루트 노드 옆에 하위 노드 개수 표시 (체크 시 "체크 수/전체 수")
//  ※ 프로그램 시작 시 ParameterSetting.json 조건으로 Run 목록을 자동 검색하여 트리에 표시
//     (ParameterForm의 "검색" 버튼과 동일한 조회)
//  만든이: 이선우
// ════════════════════════════════════════════════════════════════
using System;
using System.Collections.Generic;
using System.Drawing;
using System.IO;
using System.Threading;
using System.Threading.Tasks;
using System.Windows.Forms;
using Iruza.src.Parameter;
using System.Runtime.InteropServices;
using CheckBoxState = System.Windows.Forms.VisualStyles.CheckBoxState;

namespace Iruza
{
    // 탐색 트리, 분석 탭 및 비동기 로딩 화면을 통합하는 응용 프로그램 기본 창입니다.
    public class MainShell : Form
    {
        private TabControl _tabs;
        private TreeView _tree;

        private Panel _leftPanel;

        // ── 로딩 오버레이 (별도 스레드 기반) ──
        private Thread _loadingThread;
        private LoadingOverlayForm _loadingForm;
        private readonly object _loadingLock = new object();

        private TreeNode _root;

        // 데이터가 없을 때 루트 아래에 넣는 placeholder 노드 텍스트
        private const string NoDataText = "데이터 없음";

        // 파라미터 설정 파일 경로 (ParameterForm과 동일한 위치)
        private static string ParameterFilePath =>
            Path.Combine(Application.StartupPath, "Parameter", "ParameterSetting.json");

        MeasurementViewerPanel _sourcePanel;
        MeasurementViewerPanel _biasPanel;

        ParameterForm _ParaDlg;

        short _stepNum = 0;
        double _minPower = 0;
        double _maxPower = 0;

        string _recipeName = "";
        // ── 센서 선택 (ParameterForm의 Input sensor / Output sensor 라디오 버튼) ──
        SensorType _sensorType = SensorType.None;

        /// <summary>현재 선택된 센서 종류</summary>
        public SensorType CurrentSensorType => _sensorType;
        public bool IsInputSensor => _sensorType == SensorType.Input;
        public bool IsOutputSensor => _sensorType == SensorType.Output;

        [DllImport("user32.dll", CharSet = CharSet.Auto)]
        private static extern IntPtr SendMessage(IntPtr hWnd, int msg, IntPtr wParam, IntPtr lParam);

        private const int TVM_SETEXTENDEDSTYLE = 0x1100 + 44;
        private const int TVS_EX_DOUBLEBUFFER = 0x0004;

        Label _biasLabel;
        Label _sourceLabel;

        private sealed class LoadedRunData
        {
            public string Name { get; set; }
            public MeasurementDataset SourceDataset { get; set; }
            public MeasurementDataset BiasDataset { get; set; }
            public string SourceStatus { get; set; }
            public string BiasStatus { get; set; }
        }

        private bool _isCheckPropagating = false; // 재귀 호출/이벤트 중복 방지 플래그

        // 메인 메뉴와 탭·트리 컨트롤을 도킹 순서에 맞춰 초기화합니다.
        public MainShell()
        {
            Text = "RF Impedance Analyzer ";
            MinimumSize = new Size(1000, 650);
            StartPosition = FormStartPosition.CenterScreen;
            WindowState = FormWindowState.Maximized;   // 기동 시 모니터 전체 채움
            BackColor = Color.White;
            Font = new Font("Malgun Gothic", 9f);
            ApplyAppIcon();   // 타이틀바·작업 표시줄 아이콘 (H&iruja)

            _tree = new TreeView
            {
                Dock = DockStyle.Fill,
                Font = new Font("Malgun Gothic", 9.5f),
                BorderStyle = BorderStyle.None,
                HideSelection = false,
                FullRowSelect = true,
                ShowLines = true,
                CheckBoxes = false,
                ItemHeight = 26,
                DrawMode = TreeViewDrawMode.OwnerDrawAll
            };

            _tree.HandleCreated += (s, e) => EnableTreeViewDoubleBuffer(_tree);
            _tree.DrawNode += Tree_DrawNode;
            _tree.MouseDown += Tree_MouseDown;

            BuildMenu();
            BuildTabs();   // Dock=Fill → 반드시 먼저 Controls.Add
            BuildTree();   // Dock=Left → 그 다음에 Controls.Add

            // [ADD] 화면이 표시된 직후 ParameterSetting.json 조건으로 Run 목록 자동 검색
            //       (생성자에서 DB 조회를 하면 창이 뜨기 전에 멈춰 보이므로 Shown 시점에 비동기로 실행)
            Shown += async (s, e) => await ReloadRunNodesFromSettingAsync();
        }
        // ── 응용 프로그램 아이콘 (H&iruja) ──
        private const string AppIconFileName = "iruja.ico";

        private void ApplyAppIcon()
        {
            try
            {
                System.Drawing.Icon icon = LoadAppIcon();
                if (icon != null) Icon = icon;
            }
            catch
            {
                // 아이콘 로드 실패는 프로그램 동작에 영향을 주지 않으므로 무시합니다.
            }
        }

        /// <summary>다른 폼(ParameterForm 등)에서도 같은 아이콘을 쓸 수 있도록 공개합니다.</summary>
        public static System.Drawing.Icon LoadAppIcon()
        {
            var asm = typeof(MainShell).Assembly;
            foreach (string name in asm.GetManifestResourceNames())
            {
                if (!name.EndsWith(AppIconFileName, StringComparison.OrdinalIgnoreCase)) continue;
                using (Stream s = asm.GetManifestResourceStream(name))
                {
                    if (s != null) return new System.Drawing.Icon(s);
                }
            }

            string path = Path.Combine(Application.StartupPath, AppIconFileName);
            if (File.Exists(path)) return new System.Drawing.Icon(path);

            return System.Drawing.Icon.ExtractAssociatedIcon(Application.ExecutablePath);
        }

        // ── 파라미터 설정 로드 / 적용 ─────────────────────────────────
        /// <summary>ParameterSetting.json 을 읽습니다. 실패하면 null 을 반환합니다.</summary>
        private ParameterSetting TryLoadParameterSetting(out string error)
        {
            error = null;
            try
            {
                return ParameterSetting.Load(ParameterFilePath);
            }
            catch (Exception ex)
            {
                error = ex.Message;
                return null;
            }
        }

        /// <summary>설정값을 MainShell 필드(레시피/스텝/파워/센서)에 반영합니다.</summary>
        private void ApplyParameterSetting(ParameterSetting setting)
        {
            if (setting == null) return;

            // 저장된 센서 선택값 복원
            _sensorType = setting.Sensor ?? SensorType.None;
            OnSensorTypeChanged(_sensorType);

            // 값이 비어 있는 항목만 기본값으로 대체 (한 항목이 비었다고 전체를 초기화하지 않음)
            _recipeName = setting.RecipeName ?? "";
            _stepNum = setting.StepNum != null ? (short)setting.StepNum : (short)0;
            _minPower = setting.MinPower != null ? (double)setting.MinPower : 0;
            _maxPower = setting.MaxPower != null ? (double)setting.MaxPower : 0;
        }

        // ── Run 목록 검색 → 트리 노드 채우기 ─────────────────────────
        /// <summary>
        /// ParameterSetting.json 의 조건(레시피, 스텝, 파워 범위, 기간)으로 process_run 을 검색하여
        /// 루트 하위 노드를 다시 채웁니다. ParameterForm "검색" 버튼과 동일한 조회입니다.
        /// </summary>
        private async Task ReloadRunNodesFromSettingAsync()
        {
            var setting = TryLoadParameterSetting(out string loadError);
            if (setting == null)
            {
                FillRunNodes(new List<string>());
                MessageBox.Show(
                    "파라미터 설정 파일을 읽지 못했습니다.\n파일 → 파라미터 설정에서 조건을 지정해 주세요.\n\n" + loadError,
                    "파라미터 설정", MessageBoxButtons.OK, MessageBoxIcon.Warning);
                return;
            }

            ApplyParameterSetting(setting);

            // [FIX] ParameterForm.TryGetSearchCondition 과 동일한 규칙으로 검색 조건 구성
            //   - 비어 있는 Recipe / Step / Power 는 null(제한 없음)로 전달
            //     (기존에는 ""·0 이 그대로 필터로 들어가 Max Power=0 등으로 결과가 줄어들었음)
            //   - 기간이 없으면 ParameterForm 과 같이 최근 14일
            string recipe = string.IsNullOrWhiteSpace(setting.RecipeName) ? null : setting.RecipeName.Trim();
            short? step = (setting.StepNum.HasValue && setting.StepNum.Value > 0)
                ? (short?)setting.StepNum.Value
                : null;
            decimal? minPower = setting.MinPower;
            decimal? maxPower = setting.MaxPower;
            DateTime startTime = setting.StartTime ?? DateTime.Now.AddDays(-14);
            DateTime endTime = setting.EndTime ?? DateTime.Now;

            List<string> runNames = new List<string>();
            string dbError = null;

            ShowLoading("Run 목록 불러오는 중...");
            try
            {
                runNames = await Task.Run(() => new List<string>(
                    MeasurementDb.SearchProcessRunNames(recipe, step, minPower, maxPower, startTime, endTime)));
            }
            catch (Exception ex)
            {
                dbError = ex.Message;
            }
            finally
            {
                HideLoading();
            }

            FillRunNodes(runNames);

            if (dbError != null)
            {
                MessageBox.Show("PostgreSQL 연결 실패.\n\n" + dbError,
                    "DB 연결", MessageBoxButtons.OK, MessageBoxIcon.Warning);
            }
        }

        /// <summary>루트 하위 노드를 주어진 Run 이름으로 교체합니다. (UI 스레드에서 호출)</summary>
        private void FillRunNodes(IEnumerable<string> runNames)
        {
            _tree.BeginUpdate();
            try
            {
                _root.Checked = false;
                _root.Nodes.Clear();

                foreach (var runName in runNames)
                    _root.Nodes.Add(new TreeNode(runName));

                if (_root.Nodes.Count == 0)
                    _root.Nodes.Add(new TreeNode(NoDataText));   // 개수 표시에서는 제외되어 (0)으로 표시

                _root.Expand();
                _tree.SelectedNode = _root.Nodes[0];
            }
            finally
            {
                _tree.EndUpdate();
            }

            _tree.Invalidate();   // 루트 개수 표시 갱신
        }

        // ── 루트 하위 노드 개수 ──────────────────────────────────────
        /// <summary>"데이터 없음" placeholder를 제외한 실제 run 노드 수</summary>
        private int GetRunNodeCount()
        {
            if (_root == null) return 0;

            int count = 0;
            foreach (TreeNode n in _root.Nodes)
                if (n.Text != NoDataText) count++;
            return count;
        }

        /// <summary>체크된 run 노드 수 ("데이터 없음" 제외)</summary>
        private int GetCheckedRunNodeCount()
        {
            if (_root == null) return 0;

            int count = 0;
            foreach (TreeNode n in _root.Nodes)
                if (n.Checked && n.Text != NoDataText) count++;
            return count;
        }

        private void Tree_MouseDown(object sender, MouseEventArgs e)
        {
            TreeNode node = _tree.GetNodeAt(e.Location);
            if (node == null) return;

            var checkBoxState = node.Checked ? CheckBoxState.CheckedNormal : CheckBoxState.UncheckedNormal;
            using (var g = _tree.CreateGraphics())
            {
                Size checkSize = CheckBoxRenderer.GetGlyphSize(g, checkBoxState);

                int checkBoxX = node.Bounds.Left - checkSize.Width - 3;
                var checkArea = new Rectangle(checkBoxX, node.Bounds.Top, checkSize.Width, node.Bounds.Height);

                if (checkArea.Contains(e.Location))
                {
                    node.Checked = !node.Checked;

                    // root 노드를 체크/해제하면 모든 하위 노드에 동일하게 전파
                    if (node == _root)
                        SetChildrenChecked(node, node.Checked);

                    _tree.Invalidate();
                }
            }
        }
        private void Tree_DrawNode(object sender, DrawTreeNodeEventArgs e)
        {
            var tree = e.Node.TreeView;
            bool isSelected = (e.State & TreeNodeStates.Selected) != 0;

            var labelBounds = e.Node.Bounds;

            // 1. 배경 채우기 (행 전체 폭)
            Color backColor = isSelected ? Color.FromArgb(255, 224, 130) : tree.BackColor;
            using (var backBrush = new SolidBrush(backColor))
            {
                e.Graphics.FillRectangle(backBrush,
                    new Rectangle(0, labelBounds.Top, tree.ClientSize.Width, labelBounds.Height));
            }

            // 2. 체크박스: 라벨 왼쪽에 배치
            var checkBoxState = e.Node.Checked
                ? CheckBoxState.CheckedNormal
                : CheckBoxState.UncheckedNormal;

            Size checkSize = CheckBoxRenderer.GetGlyphSize(e.Graphics, checkBoxState);
            int checkBoxX = labelBounds.Left - checkSize.Width - 3;
            int checkBoxY = labelBounds.Top + (labelBounds.Height - checkSize.Height) / 2;

            CheckBoxRenderer.DrawCheckBox(e.Graphics, new Point(checkBoxX, checkBoxY), checkBoxState);

            // 3. 텍스트
            Color textColor = isSelected ? Color.Black : (e.Node.ForeColor == Color.Empty ? Color.Black : e.Node.ForeColor);
            Font font = e.Node.NodeFont ?? tree.Font;
            const TextFormatFlags flags = TextFormatFlags.VerticalCenter | TextFormatFlags.NoPrefix;

            TextRenderer.DrawText(e.Graphics, e.Node.Text, font, labelBounds, textColor, flags);

            // 4. 루트 노드에만 하위 노드 개수 표시  예) (35)  /  체크 시 (3/35)
            if (e.Node == _root)
            {
                int total = GetRunNodeCount();
                int checkedCnt = GetCheckedRunNodeCount();
                string countText = checkedCnt > 0 ? $"({checkedCnt}/{total})" : $"({total})";

                Size textSize = TextRenderer.MeasureText(e.Graphics, e.Node.Text, font, Size.Empty, flags);
                int countX = labelBounds.Left + textSize.Width;
                var countBounds = new Rectangle(countX, labelBounds.Top,
                                                Math.Max(0, tree.ClientSize.Width - countX), labelBounds.Height);

                TextRenderer.DrawText(e.Graphics, countText, font, countBounds,
                                      Color.FromArgb(0, 102, 204), flags | TextFormatFlags.EndEllipsis);
            }

            e.DrawDefault = false;
        }

        private void EnableTreeViewDoubleBuffer(TreeView tree)
        {
            if (tree.IsHandleCreated)
                SendMessage(tree.Handle, TVM_SETEXTENDEDSTYLE, (IntPtr)TVS_EX_DOUBLEBUFFER, (IntPtr)TVS_EX_DOUBLEBUFFER);
        }

        // ── 로딩 오버레이 (별도 스레드) ──────────────────────────────
        void ShowLoading(string message = "Loading...")
        {
            lock (_loadingLock)
            {
                if (_loadingThread != null && _loadingThread.IsAlive)
                {
                    _loadingForm?.UpdateMessage(message);
                    return;
                }

                var screenBounds = RectangleToScreen(ClientRectangle);
                var ready = new ManualResetEvent(false);

                _loadingThread = new Thread(() =>
                {
                    _loadingForm = new LoadingOverlayForm(screenBounds, message);
                    _loadingForm.HandleCreated += (s, e) => ready.Set();
                    Application.Run(_loadingForm);
                });
                _loadingThread.IsBackground = true;
                _loadingThread.SetApartmentState(ApartmentState.STA);
                _loadingThread.Start();

                ready.WaitOne(1000); // 폼 핸들 생성될 때까지 살짝 대기 (선택 사항)
            }

            UseWaitCursor = true;
            Cursor = Cursors.WaitCursor;
        }

        void HideLoading()
        {
            UseWaitCursor = false;
            Cursor = Cursors.Default;

            lock (_loadingLock)
            {
                if (_loadingForm != null && !_loadingForm.IsDisposed)
                {
                    try
                    {
                        _loadingForm.Invoke(new Action(() =>
                        {
                            Application.ExitThread(); // 이 스레드의 Application.Run 종료
                        }));
                    }
                    catch (ObjectDisposedException) { }
                    catch (InvalidOperationException) { }
                }

                _loadingThread = null;
                _loadingForm = null;
            }
        }

        List<LoadedRunData> LoadCheckedRunData(List<string> checkedRunNames)
        {
            var result = new List<LoadedRunData>();
            // 센서에 따라 조회할 채널 이름 결정 (None 은 Input 과 동일)
            bool isOutput = _sensorType == SensorType.Output;
            string sourceChannel = isOutput ? "source_out" : "source";
            string biasChannel = isOutput ? "bias_out" : "bias";

            // [FIX] 기존에는 _ParaDlg 가 null 인 상태(프로그램 시작 직후)에서 Output 센서이면
            //       _ParaDlg.getStepNum() 호출로 NullReferenceException 이 발생했음.
            //       → ParameterForm 이 있으면 그 값을, 없으면 ParameterSetting.json 에서 읽은 필드 값을 사용
            var paraDlg = _ParaDlg;

            foreach (var name in checkedRunNames)
            {
                var processRun = MeasurementDb.GetProcessRunByName(name);
                if (processRun == null)
                    continue;

                Func<string, MeasurementDataset> load;
                if (paraDlg != null)
                    load = ch => MeasurementDb.GetMeasurementDatasetByRunId(processRun.RunId, ch,
                                    paraDlg.getStepNum(), paraDlg.getPowerMin(), paraDlg.getPowerMax(), 50);
                else
                    load = ch => MeasurementDb.GetMeasurementDatasetByRunId(processRun.RunId, ch,
                                    _stepNum, _minPower, _maxPower, 50);

                result.Add(new LoadedRunData
                {
                    Name = name,
                    SourceDataset = load(sourceChannel),
                    BiasDataset = load(biasChannel),
                });
            }

            return result;
        }

        /// <summary>
        /// 센서 선택값이 확정되었을 때 호출됩니다.
        /// </summary>
        void OnSensorTypeChanged(SensorType sensorType)
        {
            switch (sensorType)
            {
                case SensorType.Input:
                    Text = "RF Impedance Analyzer";
                    // TODO: Input sensor 선택 시 처리
                    _sourceLabel.Text = "source(Input sensor)";
                    _biasLabel.Text = "bias(Input sensor)";
                    break;

                case SensorType.Output:
                    Text = "RF Impedance Analyzer";
                    // TODO: Output sensor 선택 시 처리
                    _sourceLabel.Text = "source(Output sensor)";
                    _biasLabel.Text = "bias(Output sensor)";
                    break;

                default:
                    Text = "RF Impedance Analyzer ";    
                    _sourceLabel.Text = "source(Input sensor)";
                    _biasLabel.Text = "bias(Input sensor)";
                    break;
            }
        }


        // ── 메뉴바 ──
        void BuildMenu()
        {
            var menu = new MenuStrip();

            var mFile = new ToolStripMenuItem("파일(&F)");

            mFile.DropDownItems.Add("파라미터 설정", null, (s, e) =>
            {
                GetDataViewer()?.SaveChartPng();

                _ParaDlg = new ParameterForm(_root, _recipeName, _stepNum, _minPower, _maxPower, _sensorType);

                // 검색 버튼으로 닫힌 경우(DialogResult.OK)에만 반영
                if (_ParaDlg.ShowDialog(this) == DialogResult.OK)
                {
                    // [ADD] 검색 시 저장된 설정을 필드에도 반영 → 다음에 파라미터 창을 열 때 최신 값으로 표시
                    var setting = TryLoadParameterSetting(out _);
                    if (setting != null) ApplyParameterSetting(setting);

                    _sensorType = _ParaDlg.SelectedSensor;
                    OnSensorTypeChanged(_sensorType);
                }

                // ParameterForm에서 루트 하위 노드가 다시 채워졌을 수 있으므로 개수 표시 갱신
                _tree.Invalidate();
            });


            mFile.DropDownItems.Add(new ToolStripSeparator());
            mFile.DropDownItems.Add("종료(&X)", null, (s, e) => Close());

            var mHelp = new ToolStripMenuItem("도움말(&H)");
            mHelp.DropDownItems.Add("버전 정보", null, (s, e) =>
                MessageBox.Show(
                    "Iruza RF Smith Chart Analyzer  v1.0\n\nH&iruja Inc.\nRF 임피던스 매칭 / Plasma Fingerprint 분석 솔루션",
                    "버전 정보", MessageBoxButtons.OK, MessageBoxIcon.Information));

            menu.Items.Add(mFile);
            menu.Items.Add(mHelp);
            MainMenuStrip = menu;
            Controls.Add(menu);
        }

        // ── 탭 구성 (Dock.Fill 이므로 항상 먼저 Controls 에 추가) ──
        void BuildTabs()
        {
            _tabs = new TabControl
            {
                Dock = DockStyle.Fill,
                Font = new Font("Malgun Gothic", 9.5f),
                Padding = new Point(14, 6)
            };


            var t2 = new TabPage("측정 데이터 뷰어");

            var splitSourceBias = new SplitContainer
            {
                Dock = DockStyle.Fill,
                Orientation = Orientation.Horizontal,
                FixedPanel = FixedPanel.None,
                Panel1MinSize = 100,
                Panel2MinSize = 100
            };

            _sourceLabel = new Label
            {
                Text = "Source",
                Dock = DockStyle.Top,
                Height = 15,
                Font = new Font("Malgun Gothic", 9f, FontStyle.Bold),
                TextAlign = ContentAlignment.MiddleLeft,
                Padding = new Padding(6, 0, 0, 0)
            };

            _sourcePanel = new MeasurementViewerPanel(0, _root, true) { Dock = DockStyle.Fill };

            var sourceContainer = new Panel { Dock = DockStyle.Fill };
            sourceContainer.Controls.Add(_sourcePanel);   // Fill → 먼저 추가
            sourceContainer.Controls.Add(_sourceLabel);   // Top  → 나중에 추가

            _biasLabel = new Label
            {
                Text = "Bias",
                Dock = DockStyle.Top,
                Height = 15,
                Font = new Font("Malgun Gothic", 9f, FontStyle.Bold),
                TextAlign = ContentAlignment.MiddleLeft,
                Padding = new Padding(6, 0, 0, 0)
            };

            _biasPanel = new MeasurementViewerPanel(1, _root, true) { Dock = DockStyle.Fill };

            var biasContainer = new Panel { Dock = DockStyle.Fill };
            biasContainer.Controls.Add(_biasPanel);   // Fill → 먼저 추가
            biasContainer.Controls.Add(_biasLabel);   // Top  → 나중에 추가


            splitSourceBias.Panel1.Controls.Add(sourceContainer);
            splitSourceBias.Panel2.Controls.Add(biasContainer);

            t2.Controls.Add(splitSourceBias);

            this.Shown += (s, e) =>
            {
                if (splitSourceBias.Height > 0)
                    splitSourceBias.SplitterDistance = splitSourceBias.Height / 2;
            };

            _tabs.TabPages.AddRange(new[] { t2 });


            _tabs.SelectedIndexChanged += (s, e) =>
            {
                if (_tree == null || _tree.Nodes.Count == 0) return;
                var root = _tree.Nodes[0];
                if (_tabs.SelectedIndex >= 0 && _tabs.SelectedIndex < root.Nodes.Count)
                    _tree.SelectedNode = root.Nodes[_tabs.SelectedIndex];
            };

            Controls.Add(_tabs);   // Dock=Fill → 가장 먼저 추가
        }

        // ── 좌측 트리 메뉴 (Dock.Left 이므로 탭 다음에 Controls 에 추가) ──
        void BuildTree()
        {

            _root = new TreeNode("Smith Chart");

            // [CHANGE] Run 목록은 폼이 표시된 뒤(Shown) ReloadRunNodesFromSettingAsync()에서 채움.
            //          여기서는 placeholder 만 넣어 둠.
            _root.Nodes.Add(new TreeNode(NoDataText));
            _tree.Nodes.Add(_root);
            _root.Expand();
            _tree.SelectedNode = _root.Nodes[0];

            // 트리 노드 선택 → 선택시에 코드내부로 route를 탄다. 선택한 Tree node알아 내기 
            _tree.AfterSelect += (s, e) =>
            {
                if (e.Node == null || e.Node.Parent == null) return;

            };

            _leftPanel = new Panel
            {
                Dock = DockStyle.Left,
                Width = 220,
                BackColor = Color.WhiteSmoke,
                Padding = new Padding(6, 6, 4, 6)
            };

            var bottomButtonPanel = new TableLayoutPanel
            {
                Dock = DockStyle.Bottom,
                Height = 32,
                ColumnCount = 2,
                RowCount = 1
            };
            bottomButtonPanel.ColumnStyles.Add(new ColumnStyle(SizeType.Percent, 100F));

             var btnSearch = new Button
            {
                Text = "VIEW",
                Dock = DockStyle.Fill,
                Font = new Font("Malgun Gothic", 9.5f)
            };
            btnSearch.Click += async (s, e) =>
            {
                var checkedRunNames = new List<string>();

                foreach (TreeNode node in _root.Nodes)
                {
                    // "데이터 없음" placeholder는 DB 조회 대상에서 제외
                    if (node.Checked && node.Text != NoDataText)
                        checkedRunNames.Add(node.Text);

                }

                if (checkedRunNames.Count == 0)
                {
                    MessageBox.Show("선택된 항목이 없습니다.", "검색",
                    MessageBoxButtons.OK, MessageBoxIcon.Information);

                    _sourcePanel.RemoveAllDatasets();
                    _biasPanel.RemoveAllDatasets();
                    return;
                }

                try
                {
                    btnSearch.Enabled = false;
                    ShowLoading("Smith Chart 데이터 불러오는 중...");

                    var loadedRuns = await Task.Run(() => LoadCheckedRunData(checkedRunNames));

                    _sourcePanel.RemoveAllDatasets();
                    _biasPanel.RemoveAllDatasets();

                    foreach (var run in loadedRuns)
                    {

                        _sourcePanel.OverlappedChartDisplay(0, _root, run.Name, run.SourceDataset);
                        _biasPanel.OverlappedChartDisplay(1, _root, run.Name, run.BiasDataset);
                    }
                }
                catch (Exception ex)
                {
                    MessageBox.Show("데이터 로딩 중 오류가 발생했습니다.\n\n" + ex.Message,
                        "Loading", MessageBoxButtons.OK, MessageBoxIcon.Error);
                }
                finally
                {
                    HideLoading();
                    btnSearch.Enabled = true;
                }

            };

            bottomButtonPanel.Controls.Add(btnSearch, 0, 0);

            _leftPanel.Controls.Add(_tree);
            _leftPanel.Controls.Add(bottomButtonPanel);

            Controls.Add(_leftPanel);   // Dock=Left → _tabs(Fill) 다음에 추가
        }

        /// <summary>
        ///  check가 된 Data만이 스미스차트를 그리고, data를 화면에 표시한다.
        /// </summary>
        /// <param name="sender"></param>
        /// <param name="e"></param>
        private void tree_AfterCheck(object sender, TreeViewEventArgs e)
        {
            if (_isCheckPropagating) return;

            _isCheckPropagating = true;
            try
            {
                if (e.Node == _root)
                    SetChildrenChecked(e.Node, e.Node.Checked);
                _tree.Invalidate();
            }
            finally
            {
                _isCheckPropagating = false;
            }
        }

        void SetChildrenChecked(TreeNode node, bool isChecked)
        {
            foreach (TreeNode child in node.Nodes)
            {
                child.Checked = isChecked;
                SetChildrenChecked(child, isChecked); // 손자 노드가 있는 구조라면 재귀로 계속 전파
            }
        }

        private void GetCheckedNodes(TreeNodeCollection nodes, List<string> checkedNodes)
        {
            foreach (TreeNode node in nodes)
            {
                if (node.Checked)
                    checkedNodes.Add(node.Text);

                GetCheckedNodes(node.Nodes, checkedNodes);
            }
        }

        MeasurementViewerPanel GetDataViewer()
        {
            foreach (TabPage tp in _tabs.TabPages)
                foreach (Control c in tp.Controls)
                    if (c is MeasurementViewerPanel mv) return mv;
            return null;
        }

        private void InitializeComponent()
        {
            this.SuspendLayout();     
            this.ClientSize = new System.Drawing.Size(886, 548);
            this.Name = "MainShell";
            this.ResumeLayout(false);
        }
    }
}
