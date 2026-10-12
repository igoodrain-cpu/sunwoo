// ════════════════════════════════════════════════════════════════
//  MainShell.cs  –  탭 기반 메인 셸 폼
//  탭 1 : Plasma Fingerprint 분석
//  탭 2 : 측정 데이터 뷰어 (15컬럼)
//  탭 3 : RF 임피던스 매칭 계산기
//  ※ 좌측 TreeView 네비게이션 (SplitContainer 제거 → 단순 Dock 방식 + 올바른 추가 순서로 재구성)
//  ※ 로딩 오버레이: 별도 스레드(LoadingOverlayForm)에서 실행되어
//     메인 스레드의 차트 렌더링 시간과 무관하게 Marquee 애니메이션이 끊기지 않음
//  ※ 루트 노드 옆에 하위 노드 개수 표시 (체크 시 "체크 수/전체 수")
//  만든이: 이선우
// ════════════════════════════════════════════════════════════════
using System;
using System.Collections.Generic;
using System.Drawing;
using System.IO;
using System.Runtime.Remoting.Channels;
using System.Threading;
using System.Threading.Tasks;
using System.Windows.Forms;
using System.Xml.Linq;
using Iruza.src.Parameter;
using System.Runtime.InteropServices;
using CheckBoxState = System.Windows.Forms.VisualStyles.CheckBoxState;
//using System.Windows.Forms.VisualStyles;

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




        // 클래스 상단에 추가
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
                //CheckBoxes = true,
                CheckBoxes = false,
                ItemHeight = 26,
                DrawMode = TreeViewDrawMode.OwnerDrawAll   // ← 추가
            };

            _tree.HandleCreated += (s, e) => EnableTreeViewDoubleBuffer(_tree);
            _tree.DrawNode += Tree_DrawNode;
            _tree.MouseDown += Tree_MouseDown;   // ← NodeMouseClick 대신 MouseDown

            BuildMenu();
            BuildTabs();   // Dock=Fill → 반드시 먼저 Controls.Add
            BuildTree();   // Dock=Left → 그 다음에 Controls.Add

            //_tree.AfterCheck += tree_AfterCheck;

        }
        // ── 응용 프로그램 아이콘 (H&iruja) ──
        private const string AppIconFileName = "iruja.ico";

        // 폼 아이콘을 H&iruja 아이콘으로 설정합니다.
        // 1) 어셈블리에 포함된 리소스(빌드 작업: 포함 리소스)  2) 실행 파일 폴더의 iruja.ico
        // 3) 실행 파일 자체 아이콘 순서로 찾으며, 모두 실패하면 기본 아이콘을 유지합니다.
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
                    {
                        SetChildrenChecked(node, node.Checked);
                    }

                    // 전체 트리를 다시 그려서 하위 노드들  체크박스 + 루트 개수 표시까지 화면에 반영
                    _tree.Invalidate();
                }
            }
        }
        private void Tree_DrawNode(object sender, DrawTreeNodeEventArgs e)
        {
            var tree = e.Node.TreeView;
            bool isSelected = (e.State & TreeNodeStates.Selected) != 0;

            var labelBounds = e.Node.Bounds;   // ← 항상 안정적인 라벨 영역 (DrawMode 무관)

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

                // Node.Bounds는 원래 Text 폭 기준이므로, 라벨 텍스트 바로 뒤부터 행 끝까지 영역을 잡아 그림
                Size textSize = TextRenderer.MeasureText(e.Graphics, e.Node.Text, font, Size.Empty, flags);
                int countX = labelBounds.Left + textSize.Width;
                var countBounds = new Rectangle(countX, labelBounds.Top,
                                                Math.Max(0, tree.ClientSize.Width - countX), labelBounds.Height);

                TextRenderer.DrawText(e.Graphics, countText, font, countBounds,
                                      Color.FromArgb(0, 102, 204), flags | TextFormatFlags.EndEllipsis);
            }


            e.DrawDefault = false;
        }

        private void Tree_NodeMouseClick(object sender, TreeNodeMouseClickEventArgs e)
        {
            var checkBoxState = e.Node.Checked ? CheckBoxState.CheckedNormal : CheckBoxState.UncheckedNormal;
            using (var g = _tree.CreateGraphics())
            {
                Size checkSize = CheckBoxRenderer.GetGlyphSize(g, checkBoxState);

                // Tree_DrawNode와 동일한 계산식 사용 (일관성 유지)
                int checkBoxX = e.Node.Bounds.Left - checkSize.Width - 3;
                var checkArea = new Rectangle(checkBoxX, e.Node.Bounds.Top, checkSize.Width, e.Node.Bounds.Height);

                if (checkArea.Contains(e.Location))
                {
                    e.Node.Checked = !e.Node.Checked;

                    if (e.Node == _root)
                        SetChildrenChecked(e.Node, e.Node.Checked);

                    _tree.Invalidate();
                }
            }
        }

        private void EnableTreeViewDoubleBuffer(TreeView tree)
        {
            if (tree.IsHandleCreated)
                SendMessage(tree.Handle, TVM_SETEXTENDEDSTYLE, (IntPtr)TVS_EX_DOUBLEBUFFER, (IntPtr)TVS_EX_DOUBLEBUFFER);
        }

        // ── 로딩 오버레이 (별도 스레드) ──────────────────────────────
        // 메인 UI 스레드가 차트 렌더링 등으로 오래 블로킹되어도,
        // LoadingOverlayForm은 자기만의 Application.Run 메시지 루프에서
        // 돌아가기 때문에 Marquee 애니메이션이 멈추지 않는다.
        void ShowLoading(string message = "Loading...")
        {
            lock (_loadingLock)
            {
                if (_loadingThread != null && _loadingThread.IsAlive)
                {
                    _loadingForm?.UpdateMessage(message);
                    return;
                }

                // 메인 폼 위에 겹칠 위치/크기를 UI 스레드에서 미리 계산해 넘겨준다
                // (Rectangle은 값 타입이라 스레드 간 전달에 문제 없음)
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
            //var detector = new Demo();
            // 현재 선택된 센서 (Input / Output) — 데이터 조회 조건에 필요하면 사용
            var sensorType = _sensorType;


            foreach (var name in checkedRunNames)
            {
                var processRun = MeasurementDb.GetProcessRunByName(name);
                if (processRun == null)
                    continue;


                if (_ParaDlg != null)
                {
                    var processSteps = MeasurementDb.GetProcessStepsByRunId(processRun.RunId, _ParaDlg.getStepNum());

                    if(sensorType == SensorType.Input)
                    {
                        var sourceDataset = MeasurementDb.GetMeasurementDatasetByRunId(processRun.RunId, "source", _ParaDlg.getStepNum(), _ParaDlg.getPowerMin(), _ParaDlg.getPowerMax(), 50);
                        var biasDataset = MeasurementDb.GetMeasurementDatasetByRunId(processRun.RunId, "bias", _ParaDlg.getStepNum(), _ParaDlg.getPowerMin(), _ParaDlg.getPowerMax(), 50);

                        result.Add(new LoadedRunData
                        {
                            Name = name,
                            SourceDataset = sourceDataset,
                            BiasDataset = biasDataset,
                        });
                    }

                    if (sensorType == SensorType.Output)
                    {
                        var sourceDataset = MeasurementDb.GetMeasurementDatasetByRunId(processRun.RunId, "source_out", _ParaDlg.getStepNum(), _ParaDlg.getPowerMin(), _ParaDlg.getPowerMax(), 50);
                        var biasDataset = MeasurementDb.GetMeasurementDatasetByRunId(processRun.RunId, "bias_out", _ParaDlg.getStepNum(), _ParaDlg.getPowerMin(), _ParaDlg.getPowerMax(), 50);

                        result.Add(new LoadedRunData
                        {
                            Name = name,
                            SourceDataset = sourceDataset,
                            BiasDataset = biasDataset,
                        });
                    }

                }
                else
                {

                    if (sensorType == SensorType.Input)
                    {
                        var processSteps = MeasurementDb.GetProcessStepsByRunId(processRun.RunId, _stepNum);
                        var sourceDataset = MeasurementDb.GetMeasurementDatasetByRunId(processRun.RunId, "source", _stepNum, _minPower, _maxPower, 50);
                        var biasDataset = MeasurementDb.GetMeasurementDatasetByRunId(processRun.RunId, "bias", _stepNum, _minPower, _maxPower, 50);

                        result.Add(new LoadedRunData
                        {
                            Name = name,
                            SourceDataset = sourceDataset,
                            BiasDataset = biasDataset,
                        });
                    }

                    if (sensorType == SensorType.Output)
                    {
                        var sourceDataset = MeasurementDb.GetMeasurementDatasetByRunId(processRun.RunId, "source_out", _ParaDlg.getStepNum(), _ParaDlg.getPowerMin(), _ParaDlg.getPowerMax(), 50);
                        var biasDataset = MeasurementDb.GetMeasurementDatasetByRunId(processRun.RunId, "bias_out", _ParaDlg.getStepNum(), _ParaDlg.getPowerMin(), _ParaDlg.getPowerMax(), 50);

                        result.Add(new LoadedRunData
                        {
                            Name = name,
                            SourceDataset = sourceDataset,
                            BiasDataset = biasDataset,
                        });
                    }

                    if (sensorType == SensorType.None)
                    {
                        //_sourceLabel.Text = "source(Input sensor)";
                        //_biasLabel.Text = "bias(Input sensor)";

                        var processSteps = MeasurementDb.GetProcessStepsByRunId(processRun.RunId, _stepNum);
                        var sourceDataset = MeasurementDb.GetMeasurementDatasetByRunId(processRun.RunId, "source", _stepNum, _minPower, _maxPower, 50);
                        var biasDataset = MeasurementDb.GetMeasurementDatasetByRunId(processRun.RunId, "bias", _stepNum, _minPower, _maxPower, 50);

                        result.Add(new LoadedRunData
                        {
                            Name = name,
                            SourceDataset = sourceDataset,
                            BiasDataset = biasDataset,
                        });
                    }
                }

            }

            return result;
        }
        /// <summary>
        /// 센서 선택값이 확정되었을 때 호출됩니다.
        /// Input / Output 에 따라 처리할 내용을 여기에 작성하세요.
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

                // 검색 버튼으로 닫힌 경우(DialogResult.OK)에만 센서 선택값 반영
                if (_ParaDlg.ShowDialog(this) == DialogResult.OK)
                {
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

            Controls.Add(_tabs);   // [FIX] Dock=Fill → 가장 먼저 추가
        }

        // ── 좌측 트리(그리드 트리) 메뉴 (Dock.Left 이므로 탭 다음에 Controls 에 추가) ──
        void BuildTree()
        {

            _root = new TreeNode("Smith Chart");

            // PostgreSQL의 process_run 데이터를 트리 노드로 로드
            try
            {
                var parameterPath = Path.Combine(Application.StartupPath, "Parameter", "ParameterSetting.json");
                var parameterSetting = ParameterSetting.Load(parameterPath);

                var startTime = parameterSetting.StartTime;
                var endTime = parameterSetting.EndTime;
                // 저장된 센서 선택값 복원
                _sensorType = parameterSetting.Sensor ?? SensorType.None;
                OnSensorTypeChanged(_sensorType);

                if (parameterSetting.StepNum == null || parameterSetting.MinPower == null || parameterSetting.MaxPower == null || parameterSetting.RecipeName == null)
                {
                    _recipeName = "";
                    _stepNum = 0;
                    _minPower = 0;
                    _maxPower = 0;

                }
                else
                {
                    _stepNum = (short)parameterSetting.StepNum;
                    _minPower = (double)parameterSetting.MinPower;
                    _maxPower = (double)parameterSetting.MaxPower;
                    _recipeName = parameterSetting.RecipeName;
                }

                foreach (var runName in MeasurementDb.SearchProcessRunNames(_recipeName, _stepNum, (Decimal)_minPower, (Decimal)_maxPower, startTime, endTime))
                    _root.Nodes.Add(new TreeNode(runName));

            }
            catch (Exception ex)
            {


                MessageBox.Show(
                    "PostgreSQL 연결 실패. 샘플 데이터로 표시합니다.\n\n" + ex.Message,
                    "DB 연결",
                    MessageBoxButtons.OK,
                    MessageBoxIcon.Warning);
            }

            if (_root.Nodes.Count == 0)
                _root.Nodes.Add(new TreeNode(NoDataText));   // 개수 표시에서는 제외되어 (0)으로 표시
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
            //bottomButtonPanel.ColumnStyles.Add(new ColumnStyle(SizeType.Percent, 50F));

            // [ADD] 트리 밑에 붙일 VIEW 버튼
            var btnSearch = new Button
            {
                Text = "VIEW",
                Dock = DockStyle.Fill,
                Font = new Font("Malgun Gothic", 9.5f)
            };
            btnSearch.Click += async (s, e) =>
            {
                var checkedRunNames = new List<string>();

                // string name = node.Text;

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

            Controls.Add(_leftPanel);   // [FIX] Dock=Left → _tabs(Fill) 다음에 추가해야
                                        // 탭 영역이 이 폭만큼 정상적으로 밀려남
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
                // Root 노드를 체크/해제했을 때만 하위 노드 전체에 전파
                if (e.Node == _root)
                {
                    SetChildrenChecked(e.Node, e.Node.Checked);
                    _tree.Invalidate();          // ← 전체 트리 다시 그리기
                }
                else
                {
                    _tree.Invalidate();          // ← 루트의 체크 개수 표시도 갱신해야 하므로 전체 
                }
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
            // 
            // MainShell
            // 
            this.ClientSize = new System.Drawing.Size(886, 548);
            this.Name = "MainShell";
            this.ResumeLayout(false);

        }
    }
}
