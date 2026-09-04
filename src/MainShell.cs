// ════════════════════════════════════════════════════════════════
//  MainShell.cs  –  탭 기반 메인 셸 폼
//  탭 1 : Plasma Fingerprint 분석
//  탭 2 : 측정 데이터 뷰어 (15컬럼)
//  탭 3 : RF 임피던스 매칭 계산기
//  ※ 좌측 TreeView 네비게이션 (SplitContainer 제거 → 단순 Dock 방식 + 올바른 추가 순서로 재구성)
// ════════════════════════════════════════════════════════════════
using System;
using System.Collections.Generic;
using System.Drawing;
using System.IO;
using System.Runtime.Remoting.Channels;
using System.Threading.Tasks;
using System.Windows.Forms;
using System.Xml.Linq;
//using Iruza.Anomaly;
using Iruza.src.Parameter;
using System.Runtime.InteropServices;
using CheckBoxState = System.Windows.Forms.VisualStyles.CheckBoxState;

namespace Iruza
{
    public class MainShell : Form
    {
        private TabControl _tabs;
        private TreeView _tree; 

        private Panel _leftPanel;
        private Panel _loadingOverlay;
        private Label _loadingLabel;

        private TreeNode _root;

        MeasurementViewerPanel _sourcePanel;
        MeasurementViewerPanel _biasPanel;

        ParameterForm _ParaDlg;

        //List<ProcessRunRecord> _processRecord;

        // 클래스 상단에 추가
        [DllImport("user32.dll", CharSet = CharSet.Auto)]
        private static extern IntPtr SendMessage(IntPtr hWnd, int msg, IntPtr wParam, IntPtr lParam);

        private const int TVM_SETEXTENDEDSTYLE = 0x1100 + 44;
        private const int TVS_EX_DOUBLEBUFFER = 0x0004;

        short _stepNum = 0;

        double _minPower = 0;

        double _maxPower = 0;

        string _recipeName = "";

        private sealed class LoadedRunData
        {
            public string Name { get; set; }
            public MeasurementDataset SourceDataset { get; set; }
            public MeasurementDataset BiasDataset { get; set; }
            public string SourceStatus { get; set; }
            public string BiasStatus { get; set; }
        }

        private bool _isCheckPropagating = false; // 재귀 호출/이벤트 중복 방지 플래그

        public MainShell()
        {
            /*
            Text = "Iruza – RF Smith Chart Analyzer  |  H&iruja Inc.";
            Size = new Size(1200, 780);
            MinimumSize = new Size(1000, 650);

            StartPosition = FormStartPosition.CenterScreen;
            WindowState = FormWindowState.Maximized;   // 기동 시 모니터 전체 채움
            BackColor = Color.White;
            Font = new Font("Malgun Gothic", 9f);

            var screen = Screen.PrimaryScreen.WorkingArea;
            this.Size = new Size((int)(screen.Width * 0.9), (int)(screen.Height * 0.85));
            this.StartPosition = FormStartPosition.CenterScreen;

            BuildMenu();

            // [FIX] SplitContainer는 Panel1MinSize/SplitterDistance 검증 타이밍 문제로
            // 계속 예외가 나서 제거했습니다. 대신 WinForms의 표준 도킹 규칙(=Dock.Fill
            // 컨트롤을 먼저 추가하고, 그 다음 Dock.Left 컨트롤을 추가)을 정확히 지켜서
            // 겹침/잘림/빈 화면 문제를 근본적으로 없앴습니다.
            BuildTabs();   // [FIX] Dock=Fill → 반드시 먼저 Controls.Add
            BuildTree();   // [FIX] Dock=Left → 그 다음에 Controls.Add (탭 영역을 밀어냄)
            */

            Text = "RF Impedance Analyzer ";
            MinimumSize = new Size(1000, 650);
            StartPosition = FormStartPosition.CenterScreen;
            WindowState = FormWindowState.Maximized;   // 기동 시 모니터 전체 채움
            BackColor = Color.White;
            Font = new Font("Malgun Gothic", 9f);

            var iconBytes = Properties.Resources.RF_Impedance_Analyzer;
            if (iconBytes != null && iconBytes.Length > 0)
            {
                using (var stream = new MemoryStream(iconBytes))
                    this.Icon = new Icon(stream);
            }

          /*  _tree = new TreeView
            {
                Dock = DockStyle.Fill,
                Font = new Font("Malgun Gothic", 9.5f),
                BorderStyle = BorderStyle.None,
                HideSelection = false,
                FullRowSelect = true,
                ShowLines = true,
                CheckBoxes = true,
                ItemHeight = 26
            };*/

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
            BuildLoadingOverlay();

            //_tree.AfterCheck += tree_AfterCheck;

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

                    // 전체 트리를 다시 그려서 하위 노드들 체크박스까지 화면에 반영
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

            TextRenderer.DrawText(
                e.Graphics,
                e.Node.Text,
                e.Node.NodeFont ?? tree.Font,
                labelBounds,
                textColor,
                TextFormatFlags.VerticalCenter);

            e.DrawDefault = false;
        }

        private void EnableTreeViewDoubleBuffer(TreeView tree)
        {
            if (tree.IsHandleCreated)
                SendMessage(tree.Handle, TVM_SETEXTENDEDSTYLE, (IntPtr)TVS_EX_DOUBLEBUFFER, (IntPtr)TVS_EX_DOUBLEBUFFER);
        }

        void BuildLoadingOverlay()
        {
            _loadingOverlay = new Panel
            {
                Dock = DockStyle.Fill,
                BackColor = Color.FromArgb(140, 255, 255, 255),
                Visible = false
            };

            var loadingBox = new Panel
            {
                Size = new Size(220, 80),
                BackColor = Color.White,
                BorderStyle = BorderStyle.FixedSingle
            };

            _loadingLabel = new Label
            {
                Dock = DockStyle.Fill,
                Text = "Loading...",
                Font = new Font("Malgun Gothic", 11f, FontStyle.Bold),
                TextAlign = ContentAlignment.MiddleCenter
            };

            loadingBox.Controls.Add(_loadingLabel);
            _loadingOverlay.Controls.Add(loadingBox);
            _loadingOverlay.Resize += (s, e) =>
            {
                loadingBox.Left = Math.Max(0, (_loadingOverlay.ClientSize.Width - loadingBox.Width) / 2);
                loadingBox.Top = Math.Max(0, (_loadingOverlay.ClientSize.Height - loadingBox.Height) / 2);
            };

            Controls.Add(_loadingOverlay);
            _loadingOverlay.BringToFront();
        }

        void ShowLoading(string message = "Loading...")
        {
            if (_loadingLabel != null)
                _loadingLabel.Text = message;

            if (_loadingOverlay != null)
            {
                _loadingOverlay.Visible = true;
                _loadingOverlay.BringToFront();
                _loadingOverlay.Update();
            }

            UseWaitCursor = true;
            Cursor = Cursors.WaitCursor;
        }

        void HideLoading()
        {
            UseWaitCursor = false;
            Cursor = Cursors.Default;

            if (_loadingOverlay != null)
                _loadingOverlay.Visible = false;
        }

       /* List<LoadedRunData> LoadCheckedRunData(List<string> checkedRunNames)
        {
            var result = new List<LoadedRunData>();
            var detector = new Demo();

            foreach (var name in checkedRunNames)
            {
                var processRun = MeasurementDb.GetProcessRunByName(name);
                if (processRun == null)
                    continue;

                var processSteps = MeasurementDb.GetProcessStepsByRunId(processRun.RunId);
                var sourceDataset = MeasurementDb.GetMeasurementDatasetByRunId(processRun.RunId, "source", 50, processSteps);
                var biasDataset = MeasurementDb.GetMeasurementDatasetByRunId(processRun.RunId, "bias", 50, processSteps);

                var sourceSteps = MeasurementDb.GetImpedanceStepsByRunId(processRun.RunId, "source");
                var biasSteps = MeasurementDb.GetImpedanceStepsByRunId(processRun.RunId, "bias");

                double sourceThreshold = Convert.ToDouble(MeasurementDb.GetActiveThreshold(processRun.RecipeName, "source"));
                double biasThreshold = Convert.ToDouble(MeasurementDb.GetActiveThreshold(processRun.RecipeName, "bias"));


                Demo itest = new Demo();

                List<ImpedanceStepData> iSImpedanceStepData = new List<ImpedanceStepData>();
                //string iSourceStatus = "";
                List<ImpedanceStepData> iBImpedanceStepData = new List<ImpedanceStepData>();

                //iSourceStatus
               // string iSourceStatus = itest.Run(iSImpedanceStepData, 0.55, 0.45, sourceThreshold);
               // string iBourceStatus = itest.Run(iBImpedanceStepData, 0.55, 0.45, biasThreshold);


                result.Add(new LoadedRunData
                {
                    Name = name,
                    SourceDataset = sourceDataset,
                    BiasDataset = biasDataset,
                    SourceStatus = detector.Run(sourceSteps, 0.55, 0.45, sourceThreshold),
                    BiasStatus = detector.Run(biasSteps, 0.55, 0.45, biasThreshold)
                });
            }

            return result;
        }*/

        List<LoadedRunData> LoadCheckedRunData(List<string> checkedRunNames)
        {
            var result = new List<LoadedRunData>();
            //var detector = new Demo();

            foreach (var name in checkedRunNames)
            {
                var processRun = MeasurementDb.GetProcessRunByName(name);
                if (processRun == null)
                    continue;


                if (_ParaDlg != null)
                {
                    var processSteps = MeasurementDb.GetProcessStepsByRunId(processRun.RunId, _ParaDlg.getStepNum());
                    var sourceDataset = MeasurementDb.GetMeasurementDatasetByRunId(processRun.RunId, "source", _ParaDlg.getStepNum(), _ParaDlg.getPowerMin(), _ParaDlg.getPowerMax(), 50);
                    var biasDataset = MeasurementDb.GetMeasurementDatasetByRunId(processRun.RunId, "bias", _ParaDlg.getStepNum(), _ParaDlg.getPowerMin(), _ParaDlg.getPowerMax(), 50);

                    result.Add(new LoadedRunData
                    {
                        Name = name,
                        SourceDataset = sourceDataset,
                        BiasDataset = biasDataset,
                    });
                }
                else
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

            }

            return result;
        }

        // ── 메뉴바 ──
        void BuildMenu()
        {
            var menu = new MenuStrip();

            var mFile = new ToolStripMenuItem("파일(&F)");
           // mFile.DropDownItems.Add("CSV 가져오기", null, (s, e) => GetDataViewer()?.ImportCsv());
           // mFile.DropDownItems.Add("CSV 내보내기", null, (s, e) => GetDataViewer()?.ExportCsv());
           // mFile.DropDownItems.Add(new ToolStripSeparator());
            //mFile.DropDownItems.Add("차트 PNG 저장", null, (s, e) => GetDataViewer()?.SaveChartPng());

            mFile.DropDownItems.Add("파라미터 설정", null, (s, e) =>
            {
                GetDataViewer()?.SaveChartPng();

                //_ParaDlg = new ParameterForm(_root);

                _ParaDlg = new ParameterForm(_root);
                _ParaDlg.ShowDialog();
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

            var sourceLabel = new Label
            {
                Text = "Source",
                Dock = DockStyle.Top,
                Height = 15,
                Font = new Font("Malgun Gothic", 9f, FontStyle.Bold),
                TextAlign = ContentAlignment.MiddleLeft,
                Padding = new Padding(6, 0, 0, 0)
            };
            //var sourcePanel = new MeasurementViewerPanel { Dock = DockStyle.Fill };
            _sourcePanel = new MeasurementViewerPanel(0, _root, true) { Dock = DockStyle.Fill };

            var sourceContainer = new Panel { Dock = DockStyle.Fill };
            sourceContainer.Controls.Add(_sourcePanel);   // Fill → 먼저 추가
            sourceContainer.Controls.Add(sourceLabel);   // Top  → 나중에 추가

            var biasLabel = new Label
            {
                Text = "Bias",
                Dock = DockStyle.Top,
                Height = 15,
                Font = new Font("Malgun Gothic", 9f, FontStyle.Bold),
                TextAlign = ContentAlignment.MiddleLeft,
                Padding = new Padding(6, 0, 0, 0)
            };
            //var biasPanel = new MeasurementViewerPanel { Dock = DockStyle.Fill };
            //var biasPanel = new MeasurementViewerPanel(1, _root) { Dock = DockStyle.Fill };
            _biasPanel = new MeasurementViewerPanel(1, _root, true) { Dock = DockStyle.Fill };

            var biasContainer = new Panel { Dock = DockStyle.Fill };
            biasContainer.Controls.Add(_biasPanel);   // Fill → 먼저 추가
            biasContainer.Controls.Add(biasLabel);   // Top  → 나중에 추가


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
         /*   _tree = new TreeView
            {
                Dock = DockStyle.Fill,
                Font = new Font("Malgun Gothic", 9.5f),
                BorderStyle = BorderStyle.None,
                HideSelection = false,
                FullRowSelect = true,
                ShowLines = true,
                CheckBoxes = true,
                ItemHeight = 26
            };

            _tree.AfterCheck += tree_AfterCheck;*/

            _root = new TreeNode("Smith Chart Fingerprint");
            //root.Nodes.Add(new TreeNode("Plasma Fingerprint 분석"));

           // _root.Nodes.Add(new TreeNode("20260727122030_normal"));
           // _root.Nodes.Add(new TreeNode("20260727122030_Abnormal"));

            // PostgreSQL의 process_run 데이터를 트리 노드로 로드
            try
            {
                var parameterPath = Path.Combine(Application.StartupPath, "Parameter", "ParameterSetting.json");
                //var parameterSetting = ParameterSetting.Load(parameterPath);
                var parameterSetting = ParameterSetting.LoadPara(parameterPath);

                var startTime = parameterSetting.StartTime;
                var endTime = parameterSetting.EndTime;

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

                //foreach (var runName in MeasurementDb.GetProcessRunNames(startTime, endTime))
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
                _root.Nodes.Add(new TreeNode("데이터 없음"));
            // root.Nodes.Add(new TreeNode("임피던스 매칭 계산기"));
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
            bottomButtonPanel.ColumnStyles.Add(new ColumnStyle(SizeType.Percent, 50F));
            bottomButtonPanel.ColumnStyles.Add(new ColumnStyle(SizeType.Percent, 50F));

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

                foreach (TreeNode node in _root.Nodes)
                {
                    if (node.Checked)
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
                    ShowLoading("Loading...");

                    var loadedRuns = await Task.Run(() => LoadCheckedRunData(checkedRunNames));

                    _sourcePanel.RemoveAllDatasets();
                    _biasPanel.RemoveAllDatasets();

                    foreach (var run in loadedRuns)
                    {
                        _sourcePanel.OverlappedChartDisplay(0, _root, run.Name, run.SourceDataset, run.SourceStatus);
                        _biasPanel.OverlappedChartDisplay(1, _root, run.Name, run.BiasDataset, run.BiasStatus);
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

            var btnLearning = new Button
            {
                Text = "LEARNING",
                Dock = DockStyle.Fill,
                Font = new Font("Malgun Gothic", 9.5f)
            };
            btnLearning.Click += async (s, e) =>
            {
                var goldenRunIds = new List<long>();
                string irecipeName = "";

                foreach (TreeNode node in _root.Nodes)
                {
                    string name = node.Text;
                    if (node.Checked)
                    {
                        ProcessRunRecord iprocessRunRecord = new ProcessRunRecord();
                        iprocessRunRecord = MeasurementDb.GetProcessRunByName(name);

                        if (iprocessRunRecord != null)
                        {
                            goldenRunIds.Add(iprocessRunRecord.RunId);
                            irecipeName = iprocessRunRecord.RecipeName;
                        }
                    }
                }

                if (goldenRunIds.Count == 0)
                {
                    MessageBox.Show("선택된 항목이 없습니다.", "LEARNING",
                        MessageBoxButtons.OK, MessageBoxIcon.Information);
                    return;
                }

                try
                {
                    btnSearch.Enabled = false;
                    btnLearning.Enabled = false;
                    ShowLoading("Learning...");

                    await Task.Run(() =>
                    {
                        double sourceThreshold = ImpedanceAnomalyDetector.CalibrateThresholdFromGoldenRuns(
                            goldenRunIds, channel: "source", percentile: 97.0);

                        double biasThreshold = ImpedanceAnomalyDetector.CalibrateThresholdFromGoldenRuns(
                            goldenRunIds, channel: "bias", percentile: 97.0);

                        MeasurementDb.SaveCalibratedThreshold(irecipeName, "source", sourceThreshold, 97.0, goldenRunIds.Count, goldenRunIds, "UserA");
                        MeasurementDb.SaveCalibratedThreshold(irecipeName, "bias", biasThreshold, 97.0, goldenRunIds.Count, goldenRunIds, "UserA");
                    });

                    MessageBox.Show("LEARNING이 완료 되었습니다.", "LEARNING",
                        MessageBoxButtons.OK, MessageBoxIcon.Information);
                }
                catch (Exception ex)
                {
                    MessageBox.Show("LEARNING 중 오류가 발생했습니다.\n\n" + ex.Message,
                        "LEARNING", MessageBoxButtons.OK, MessageBoxIcon.Error);
                }
                finally
                {
                    HideLoading();
                    btnSearch.Enabled = true;
                    btnLearning.Enabled = true;
                }
            };

            bottomButtonPanel.Controls.Add(btnSearch, 0, 0);
            bottomButtonPanel.Controls.Add(btnLearning, 1, 0);

            _leftPanel.Controls.Add(_tree);
            _leftPanel.Controls.Add(bottomButtonPanel);

            Controls.Add(_leftPanel);   // [FIX] Dock=Left → _tabs(Fill) 다음에 추가해야
                                        // 탭 영역이 이 폭만큼 정상적으로 밀려남
        }

        /// <summary>
        /// MainShell의 메뉴/버튼 등에서 호출하는 진입점 예시.
        /// 실제로는 run_id 목록을 DB 조회(예: 최근 N개월 중 알람 없이 종료된 run)로 채우거나,
        /// 엔지니어가 UI에서 체크박스로 선택한 run들을 넘겨받는 형태가 됩니다.
        /// </summary>
        public static void RunCalibrationDemo()
        {
            // 1) 골든 런 run_id 목록 (예시 — 실제로는 DB에서 조회하거나 UI에서 선택)
            var goldenRunIds = new List<long> { 101, 102, 103, 104, 105 };

            // 2) 채널별로 각각 캘리브레이션 (Source/Bias는 특성이 다르므로 분리)
            double sourceThreshold = ImpedanceAnomalyDetector.CalibrateThresholdFromGoldenRuns(
                goldenRunIds, channel: "source", percentile: 97.0);

            double biasThreshold = ImpedanceAnomalyDetector.CalibrateThresholdFromGoldenRuns(
                goldenRunIds, channel: "bias", percentile: 97.0);

            Console.WriteLine($"Source 채널 캘리브레이션 threshold (97th pct): {sourceThreshold:F4}");
            Console.WriteLine($"Bias   채널 캘리브레이션 threshold (97th pct): {biasThreshold:F4}");

            // 3) 캘리브레이션된 threshold를 신규(라이브) 런 판정에 적용
            long liveRunId = 201; // 예: 방금 종료된 신규 run
            var liveSteps = MeasurementDb.GetImpedanceStepsByRunId(liveRunId, "bias");

            if (liveSteps.Count < 2)
            {
                Console.WriteLine("스텝 데이터가 부족하여 판정을 건너뜁니다.");
                return;
            }

            var results = ImpedanceAnomalyDetector.DetectAnomalies(liveSteps, threshold: biasThreshold);

            Console.WriteLine($"\n[Run {liveRunId} / Bias] 판정 결과");
            Console.WriteLine($"{"Step",5} {"AnomalyScore",13} {"Label",10}");
            foreach (var r in results)
                Console.WriteLine($"{r.Step,5} {r.AnomalyScore,13:F4} {r.Label,10}");

            // 4) threshold 저장 (예: appsettings.json, DB 설정 테이블 등에 영구 저장)
            //    여기서는 저장 로직 자리만 표시 — 실제 구현 시 레시피명/장비ID 기준으로 키를 나눠 저장 권장
            // SaveThresholdToConfig(recipeName: "RecipeA", channel: "bias", threshold: biasThreshold);
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
