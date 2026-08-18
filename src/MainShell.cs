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
using System.Windows.Forms;
using System.Xml.Linq;
using Iruza.src.Parameter;

namespace Iruza
{
    public class MainShell : Form
    {
        private TabControl _tabs;
        private TreeView _tree; 

        private Panel _leftPanel;

        private TreeNode _root;

        MeasurementViewerPanel _sourcePanel;
        MeasurementViewerPanel _biasPanel;

        ParameterForm _ParaDlg;

        List<ProcessRunRecord> _processRecord; 

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

            Text = "Iruza – RF Smith Chart Analyzer  |  H&iruja Inc.";
            MinimumSize = new Size(1000, 650);
            StartPosition = FormStartPosition.CenterScreen;
            WindowState = FormWindowState.Maximized;   // 기동 시 모니터 전체 채움
            BackColor = Color.White;
            Font = new Font("Malgun Gothic", 9f);

            _tree = new TreeView
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

            BuildMenu();
            BuildTabs();   // Dock=Fill → 반드시 먼저 Controls.Add
            BuildTree();   // Dock=Left → 그 다음에 Controls.Add

            _tree.AfterCheck += tree_AfterCheck;

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
                var parameterSetting = ParameterSetting.Load(parameterPath);

                var startTime = parameterSetting.StartTime;
                var endTime = parameterSetting.EndTime;

                foreach (var runName in MeasurementDb.GetProcessRunNames(startTime, endTime))
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

                
               // switch (e.Node.Text)
               // {

                switch (e.Node.Index)
                {
                    /// DB에서 Index의 Data를 가져와야 하는 부분 

                    //case "Plasma Fingerprint 분석": _tabs.SelectedIndex = 0; break;
                    ///case "20260727122030_normal": _tabs.SelectedIndex = 1; break;
                  //  case 0: _tabs.SelectedIndex = 0; break;
                  //  case 1: _tabs.SelectedIndex = 1; break;
                        // case "20260727122030_normal1": _tabs.SelectedIndex = 1; break;
                        // case "임피던스 매칭 계산기": _tabs.SelectedIndex = 2; break;
                }
            };

            _leftPanel = new Panel
            {
                Dock = DockStyle.Left,
                Width = 220,
                BackColor = Color.WhiteSmoke,
                Padding = new Padding(6, 6, 4, 6)
            };

            // [ADD] 트리 밑에 붙일 검색 버튼
            var btnSearch = new Button
            {
                Text = "검색",
                Dock = DockStyle.Bottom,
                Height = 32,
                Font = new Font("Malgun Gothic", 9.5f)
            };
            btnSearch.Click += (s, e) =>
            {
                _processRecord = new List<ProcessRunRecord>();

                

                foreach (TreeNode node in _root.Nodes)
                {
                    string name = node.Text;
                    // Console.WriteLine(name);
                    if (node.Checked)
                    {
                        ProcessRunRecord iprocessRunRecord = new ProcessRunRecord();
                        iprocessRunRecord = MeasurementDb.GetProcessRunByName(name);

                        if(iprocessRunRecord != null)
                        {
                            List<ProcessStepRecord> iProcessStepRecord = new List<ProcessStepRecord>();
                            iProcessStepRecord = MeasurementDb.GetProcessStepsByRunId(iprocessRunRecord.RunId);


                            MeasurementDataset iSmeasurementDataset = new MeasurementDataset();
                            iSmeasurementDataset = MeasurementDb.GetMeasurementDatasetByRunId(iprocessRunRecord.RunId, "source", 50);

                            MeasurementDataset iBmeasurementDataset = new MeasurementDataset();
                            iBmeasurementDataset = MeasurementDb.GetMeasurementDatasetByRunId(iprocessRunRecord.RunId, "bias", 50);

                            _sourcePanel.OverlappedChartDisplay(0, _root, name, iSmeasurementDataset);
                            _biasPanel.OverlappedChartDisplay(1, _root, name, iBmeasurementDataset);

                        }

                       // _sourcePanel.OverlappedChart(0, _root, name);
                       // _biasPanel.OverlappedChart(1, _root, name);
                    }
                        
                }


                _processRecord = MeasurementDb.GetProcessRuns();


                foreach (TreeNode node in _root.Nodes) 
                    foreach (var runName in _processRecord)
                    {

                        if (node.ToString() == runName.RunName && node.Checked == true)
                        {
                            ProcessRunRecord iprocessRunRecord = new ProcessRunRecord();
                            iprocessRunRecord = runName;
                        }

                    }


                    // TODO: 검색 로직 연결 (예: ParameterSetting의 기간으로 MeasurementDb 재조회 후 트리 리로드)
                    //MessageBox.Show("검색 기능은 아직 구현되지 않았습니다.", "검색",
                    //MessageBoxButtons.OK, MessageBoxIcon.Information);
            };

            _leftPanel.Controls.Add(_tree);
            _leftPanel.Controls.Add(btnSearch);

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
            List<string> checkedNodes = new List<string>();

            GetCheckedNodes(_tree.Nodes, checkedNodes);

            //_sourcePanel.OverlappedChart(0, _root);

            foreach (string nodeText in checkedNodes)
            {
                Console.WriteLine(nodeText);
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
