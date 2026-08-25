// ════════════════════════════════════════════════════════════════
//  MeasurementViewerPanel.cs  –  탭2: 측정 데이터 뷰어
//  스미스차트(좌) + 15컬럼 DataGridView(우) + 통계 바
//  [CHG] 여러 MeasurementDataset을 체크박스로 선택 → 스미스차트에 겹쳐 표시
// ════════════════════════════════════════════════════════════════
using System;
using System.Collections.Generic;
using System.Drawing;
using System.Drawing.Drawing2D;
using System.Drawing.Text;
using System.Linq;
using System.Threading;
using System.Windows.Forms;

namespace Iruza
{
    public class MeasurementViewerPanel : Panel
    {
        // 이 뷰어(예: Source 패널, Bias 패널)가 보유한 데이터셋 목록
        private List<MeasurementDataset> _dsList = new List<MeasurementDataset>();

        // 그리드/통계/편집 대상이 되는 "활성" 데이터셋 인덱스 (1개만 가능)
        private int _activeDsIndex = -1;

        // [ADD] 스미스차트에 겹쳐서 표시할 데이터셋 인덱스들 (여러 개 선택 가능)
        private List<int> _selectedDsIndices = new List<int>();

        // 기존 코드 호환용 – 활성 데이터셋을 가리키는 읽기전용 프로퍼티
        private MeasurementDataset _ds =>
            (_activeDsIndex >= 0 && _activeDsIndex < _dsList.Count) ? _dsList[_activeDsIndex] : null;

        private MeasurementChartPanel _chart;
        private DataGridView _grid;
        private Label _statLbl;
        private ComboBox _cbColor;
        private CheckBox _chkOverlay;          // [ADD] 겹쳐보기 단일 체크박스
        private FlowLayoutPanel _dsCheckPanel;   // [ADD] 데이터셋 체크박스(겹쳐보기 선택) 목록
        private int _activeIdx = -1;
        private bool _isUpdatingSelection = false;

        public MeasurementViewerPanel()
        {
            BackColor = Color.White;

            _dsList = new List<MeasurementDataset> { MeasurementDataset.CreateSample("Test1") };
            _activeDsIndex = 0;
            _selectedDsIndices = new List<int> { 0 };

            BuildLayout();
            RefreshDatasetList();
            RefreshAll();
        }

        public MeasurementViewerPanel(int i, TreeNode root, bool pInit)
        {
            BackColor = Color.White;

       /*     if(pInit == false)
            {
                var initial = (i == 0)
                ? MeasurementDataset.CreateSample("Test1")
                : MeasurementDataset.CreateSampleBt("Test2");

                _dsList = new List<MeasurementDataset> { initial };
                _activeDsIndex = 0;
                _selectedDsIndices = new List<int> { 0 };
            }*/

            BuildLayout();
            RefreshDatasetList();
            RefreshAll();
        }


        public void OverlappedChartDisplay(int i, TreeNode root, string pName, MeasurementDataset pMeasurementDataset, string pStatus)
        {
            BackColor = Color.White;
            //int j = 0;


            if(i == 0)
            {
                pName = pName + "_source";
            }
            else
            {
                pName = pName + "_bias";
            }
                           

            //AddDataset(new MeasurementDataset { Z0 = 50, Name = $"Dataset{_dsList.Count + 1}" });

            foreach (MeasurementDataset dataset in _dsList)
            {
                string name = dataset.Name;
                name = name.Split('(')[0];
                if (name == pName)
                {

                    return;
                }

            }

            if (_dsList.Count == 0)
            {
                // List<MeasurementDataset> _dsList = new List<MeasurementDataset>();에 아무데이터도 없을시 MeasurementDataset initial = new MeasurementDataset();를 생성하여 _dsList에 추가
                //  var initial = (i == 0)
                //  ? MeasurementDataset.CreateSample(pName)
                // : MeasurementDataset.CreateSampleBt(pName);

                // _dsList = new List<MeasurementDataset> { initial };

                var initial = new MeasurementDataset();
                initial = pMeasurementDataset;

                _dsList = new List<MeasurementDataset> { initial };
                _activeDsIndex = 0;
                _selectedDsIndices = new List<int> { 0 };

            }
            else
            {
                var initial = new MeasurementDataset();
                initial = pMeasurementDataset;
                AddDataset(initial,true);
                //AddDataset(new MeasurementDataset { Z0 = 50, Name = pName });
            }


            //AddDataset(new MeasurementDataset { Z0 = 50, Name = pName });

            //BuildLayout();

            if (pStatus == "NORMAL")
            {
                _dsList[_dsList.Count - 1].Name = _dsList[_dsList.Count - 1].Name + "(NORMAL)";

            }
            else
            {
                _dsList[_dsList.Count - 1].Name = _dsList[_dsList.Count - 1].Name + "(ABNORMAL)";
            }

            RefreshDatasetList();
            RefreshAll();
        }

        public void OverlappedChart(int i, TreeNode root , string pName)
        {
            BackColor = Color.White;



            //AddDataset(new MeasurementDataset { Z0 = 50, Name = $"Dataset{_dsList.Count + 1}" });

            foreach (MeasurementDataset dataset in _dsList)
            {
                string name = dataset.Name;

                if(name == pName)
                {

                    return;
                }

            }

            if(_dsList.Count == 0)
            {
                // List<MeasurementDataset> _dsList = new List<MeasurementDataset>();에 아무데이터도 없을시 MeasurementDataset initial = new MeasurementDataset();를 생성하여 _dsList에 추가
                var initial = (i == 0)
                ? MeasurementDataset.CreateSample(pName)
                : MeasurementDataset.CreateSampleBt(pName);

                _dsList = new List<MeasurementDataset> { initial };


                _activeDsIndex = 0;
                _selectedDsIndices = new List<int> { 0 };
            }
            else
            {
                AddDataset(new MeasurementDataset { Z0 = 50, Name = pName });
            }


            //AddDataset(new MeasurementDataset { Z0 = 50, Name = pName });

            //BuildLayout();
            RefreshDatasetList();
            RefreshAll();
        }

        // ── 공개 메서드 (MainShell 메뉴 / 트리노드 등에서 호출) ──
        public void ImportCsv()
        {
            using var dlg = new OpenFileDialog { Filter = "CSV 파일|*.csv|모든 파일|*.*" };
            if (dlg.ShowDialog() != DialogResult.OK) return;
            try
            {
                var imported = MeasurementDataset.FromCsv(dlg.FileName);
                _dsList.Add(imported);
                _activeDsIndex = _dsList.Count - 1;
                if (!_selectedDsIndices.Contains(_activeDsIndex)) _selectedDsIndices.Add(_activeDsIndex);
                RefreshDatasetList();
                RefreshAll();
            }
            catch (Exception ex)
            {
                MessageBox.Show($"CSV 오류:\n{ex.Message}", "오류",
                    MessageBoxButtons.OK, MessageBoxIcon.Error);
            }
        }

        public void ExportCsv()
        {
            if (_ds == null) return;
            using var dlg = new SaveFileDialog { Filter = "CSV|*.csv", FileName = _ds.Name + "_export.csv" };
            if (dlg.ShowDialog() != DialogResult.OK) return;
            _ds.ToCsv(dlg.FileName);
            MessageBox.Show("CSV 저장 완료.", "내보내기", MessageBoxButtons.OK, MessageBoxIcon.Information);
        }

        public void SaveChartPng()
        {
            using var dlg = new SaveFileDialog { Filter = "PNG|*.png", FileName = "smith_chart.png" };
            if (dlg.ShowDialog() != DialogResult.OK) return;
            _chart.SaveToPng(dlg.FileName, 1200, 1200);
            MessageBox.Show("차트 저장 완료.", "저장", MessageBoxButtons.OK, MessageBoxIcon.Information);
        }

        // [ADD] 트리노드 등 외부에서 특정 데이터셋을 이 뷰어에 추가하고 싶을 때 호출
        public void AddDataset(MeasurementDataset ds, bool select = true)
        {
            if (ds == null) return;
            _dsList.Add(ds);
            _activeDsIndex = _dsList.Count - 1;
            if (select && !_selectedDsIndices.Contains(_activeDsIndex)) _selectedDsIndices.Add(_activeDsIndex);
            RefreshDatasetList();
            RefreshAll();
        }

        // [ADD] 빈 데이터셋을 새로 만들어 리스트에 추가하고 활성화 (툴바 "데이터셋 추가" 버튼)
        void AddDataset()
        {
            AddDataset(new MeasurementDataset { Z0 = 50, Name = $"Dataset{_dsList.Count + 1}" });
        }

        // [ADD] 현재 활성 데이터셋을 리스트에서 제거
        public void RemoveDataset()
        {
            if (_activeDsIndex < 0 || _activeDsIndex >= _dsList.Count) return;
            int removed = _activeDsIndex;
            _dsList.RemoveAt(removed);
           // if (_dsList.Count == 0)
           //     _dsList.Add(MeasurementDataset.CreateSample(_dsList.));

            // 삭제된 인덱스 이후 항목들의 인덱스를 1씩 당겨서 선택 목록 재정렬
            _selectedDsIndices = _selectedDsIndices
                .Where(idx => idx != removed)
                .Select(idx => idx > removed ? idx - 1 : idx)
                .Distinct()
                .ToList();
            if (_selectedDsIndices.Count == 0) _selectedDsIndices.Add(0);

            _activeDsIndex = Math.Min(removed, _dsList.Count - 1);
            RefreshDatasetList();
            RefreshAll();
        }

        /// <summary>
        ///  모든 데이터 삭제
        /// </summary>
        public void RemoveAtDatasets(int i, string pName)
        {
            //_dsList.Clear();

            if (i == 0)
            {
                pName = pName + "_source";
            }
            else
            {
                pName = pName + "_bias";
            }


            foreach (MeasurementDataset dataset in _dsList)
            {
                string name = dataset.Name;
                name = name.Split('(')[0];
                if (name == pName)
                {
                    _dsList.Remove(dataset);
                    break;
                }
            }
  
            _activeDsIndex = _dsList.Count - 1;

            RefreshDatasetList();
            RefreshAll();
        }

        /// <summary>
        ///  모든 데이터 삭제
        /// </summary>
        public void RemoveAllDatasets()
        {
            _dsList.Clear();
            _selectedDsIndices.Clear();
            _activeDsIndex = -1;

            RefreshDatasetList();
            RefreshAll();
        }

        // [ADD] 체크된(겹쳐 표시할) 데이터셋들을 (인덱스, 데이터셋) 목록으로 반환
        List<(int idx, MeasurementDataset ds)> GetOverlaySelection()
        {
            return _selectedDsIndices
                .Where(i => i >= 0 && i < _dsList.Count)
                .Distinct()
                .OrderBy(i => i)
                .Select(i => (i, _dsList[i]))
                .ToList();
        }

        // [ADD] 데이터셋 체크박스 목록을 현재 _dsList / _selectedDsIndices 상태와 동기화
        void RefreshDatasetList()
        {
            if (_dsCheckPanel == null) return;
            _dsCheckPanel.SuspendLayout();
            _dsCheckPanel.Controls.Clear();

            for (int i = 0; i < _dsList.Count; i++)
            {
                int idx = i; // 클로저 캡처용
                var cb = new CheckBox
                {
                    Text = string.IsNullOrEmpty(_dsList[i].Name) ? $"Dataset{i + 1}" : _dsList[i].Name,
                    AutoSize = true,
                    Checked = _selectedDsIndices.Contains(idx),
                    Margin = new Padding(0, 3, 12, 3),
                    Font = (idx == _activeDsIndex) ? new Font(Font, FontStyle.Bold) : Font,
                    ForeColor = MeasurementChartPanel.DatasetPalette[idx % MeasurementChartPanel.DatasetPalette.Length]
                };
                cb.CheckedChanged += (s, e) =>
                {
                    if (cb.Checked)
                    {
                        if (!_selectedDsIndices.Contains(idx)) _selectedDsIndices.Add(idx);
                        _activeDsIndex = idx; // 마지막으로 체크한 항목이 그리드/편집 대상이 됨
                    }
                    else
                    {
                        _selectedDsIndices.Remove(idx);
                        if (_activeDsIndex == idx)
                            _activeDsIndex = _selectedDsIndices.Count > 0
                                ? _selectedDsIndices[_selectedDsIndices.Count - 1]
                                : (_dsList.Count > 0 ? 0 : -1);
                    }
                    RefreshDatasetList();
                    RefreshAll();
                };
                _dsCheckPanel.Controls.Add(cb);
            }
            _dsCheckPanel.ResumeLayout();
            UpdateOverlayUiState();
        }

        void UpdateOverlayUiState()
        {
            bool enabled = _chkOverlay == null || _chkOverlay.Checked;

            if (_dsCheckPanel != null)
            {
                foreach (Control c in _dsCheckPanel.Controls)
                    c.Enabled = enabled;

                _dsCheckPanel.BackColor = enabled
                    ? Color.Transparent
                    : Color.FromArgb(245, 245, 245);
            }
        }

        void BuildLayout()
        {
            var toolbar = BuildToolbar();

            var overlayBar = new Panel
            {
                Dock = DockStyle.Top,
                Height = 52,
                BackColor = Color.FromArgb(250, 250, 252)
            };

            _chkOverlay = new CheckBox
            {
                Text = "겹쳐보기",
                AutoSize = true,
                Checked = true,
                Location = new Point(8, 15)
            };
            _chkOverlay.CheckedChanged += (s, e) =>
            {
                UpdateOverlayUiState();
                RefreshAll();
            };

            var dsLabel = new Label
            {
                Text = "데이터셋:",
                AutoSize = true,
                Location = new Point(95, 16)
            };

            // [ADD] 데이터셋 겹쳐보기 체크박스 행 (툴바 바로 아래)
            _dsCheckPanel = new FlowLayoutPanel
            {
                Location = new Point(160, 8),
                Height = 36,
                AutoScroll = true,
                FlowDirection = FlowDirection.LeftToRight,
                WrapContents = false,
                Anchor = AnchorStyles.Top | AnchorStyles.Left | AnchorStyles.Right,
                BackColor = Color.Transparent
            };

            overlayBar.Resize += (s, e) =>
            {
                int left = dsLabel.Right + 8;
                _dsCheckPanel.SetBounds(left, 8, Math.Max(80, overlayBar.ClientSize.Width - left - 6), overlayBar.ClientSize.Height - 16);
            };

            overlayBar.Controls.Add(_chkOverlay);
            overlayBar.Controls.Add(dsLabel);
            overlayBar.Controls.Add(_dsCheckPanel);

            var split = new SplitContainer
            {
                Dock = DockStyle.Fill,
                Orientation = Orientation.Vertical
            };

            this.HandleCreated += (s, e) =>
            {
                if (split.Width > 100)
                    split.SplitterDistance = (int)(split.Width * 0.5); // 차트 28% : 그리드 72%
            };

            _chart = new MeasurementChartPanel { Dock = DockStyle.Fill };
            // [CHG] 그리드 행 하이라이트는 "활성 데이터셋"의 포인트를 hover 했을 때만 반영
            _chart.StepHovered += (dsIdx, stepIdx) =>
            {
                if (dsIdx == _activeDsIndex)
                {
                    _activeIdx = stepIdx;
                    HighlightRow(stepIdx);
                }
            };
            split.Panel1.Controls.Add(_chart);

            var rightLayout = new TableLayoutPanel
            {
                Dock = DockStyle.Fill,
                RowCount = 2
            };
            rightLayout.RowStyles.Add(new RowStyle(SizeType.Percent, 100));
            rightLayout.RowStyles.Add(new RowStyle(SizeType.Absolute, 40));

            _grid = BuildGrid();
            _grid.SelectionChanged += (s, e) =>
            {
                if (_isUpdatingSelection) return;
                if (_grid.SelectedRows.Count == 0) return;
                _activeIdx = _grid.SelectedRows[0].Index;
                _chart.Highlight(_activeDsIndex, _activeIdx);
            };
            _grid.CellEndEdit += Grid_CellEndEdit;
            rightLayout.Controls.Add(_grid, 0, 0);

            _statLbl = new Label
            {
                Dock = DockStyle.Fill,
                Font = new Font("Consolas", 8f),
                TextAlign = ContentAlignment.MiddleLeft,
                Padding = new Padding(8, 0, 0, 0),
                BackColor = Color.FromArgb(245, 248, 252)
            };
            rightLayout.Controls.Add(_statLbl, 0, 1);

            split.Panel2.Controls.Add(rightLayout);

            // Dock 순서: Fill(split) → Top(체크박스 행) → Top(toolbar, 맨 위)
            Controls.Add(split);
            Controls.Add(overlayBar);
            Controls.Add(toolbar);
        }

        ToolStrip BuildToolbar()
        {
            var tb = new ToolStrip { Dock = DockStyle.Top };

            void Btn(string txt, Action act)
            {
                var b = new ToolStripButton(txt) { DisplayStyle = ToolStripItemDisplayStyle.Text };
                b.Click += (s, e) => act();
                tb.Items.Add(b);
            }

            Btn("CSV 가져오기", ImportCsv);
            tb.Items.Add(new ToolStripSeparator());
            Btn("CSV 내보내기", ExportCsv);
            //Btn("스텝 추가", AddManual);
            //Btn("선택 삭제", DeleteSelected);
            tb.Items.Add(new ToolStripSeparator());
            Btn("차트 저장 PNG", SaveChartPng);
            tb.Items.Add(new ToolStripSeparator());
           // Btn("데이터셋 추가", AddDataset);
           // Btn("데이터셋 삭제", RemoveDataset);
           // tb.Items.Add(new ToolStripSeparator());
            tb.Items.Add(new ToolStripLabel("  색상: "));
            _cbColor = new ComboBox
            {
                Width = 120,
                DropDownStyle = ComboBoxStyle.DropDownList
            };
            _cbColor.Items.AddRange(new[] { "VSWR 열지도", "단색 팔레트", "전력 그라데이션" });
            _cbColor.SelectedIndex = 0;
            _cbColor.SelectedIndexChanged += (s, e) => _chart.SetColorMode(_cbColor.SelectedIndex);
            tb.Items.Add(new ToolStripControlHost(_cbColor));
            return tb;
        }

        DataGridView BuildGrid()
        {
            var g = new DataGridView
            {
                Dock = DockStyle.Fill,
                AllowUserToAddRows = false,
                ReadOnly = false,
                SelectionMode = DataGridViewSelectionMode.FullRowSelect,
                MultiSelect = false,
                Font = new Font("Consolas", 8f),
                AutoSizeColumnsMode = DataGridViewAutoSizeColumnsMode.AllCells,
                ColumnHeadersHeightSizeMode = DataGridViewColumnHeadersHeightSizeMode.AutoSize
            };

            var cols = new[]{
                ("Step","#",true),("Vout_Vrms","Vout\nVrms",true),
                ("Iout_Arms","Iout\nArms",true),("Phase_deg","θ\ndeg",true),
                ("R","R Ω",true),("X","X Ω",true),
                ("Gamma_Real","Γ real",true),("Gamma_Imag","Γ imag",true),
                ("GammaMag","|Γ|",true),("VSWR","VSWR",true),
                ("Z_Text","Z",true),("Z_Normalized","z norm",true),
                ("ForwardP_W","Fwd W",true),("ReflectedP_W","Ref W",true),
                ("DeliveredP_W","Del W",true),("ReturnLoss_dB","RL dB",true),
                ("Efficiency_pct","η %",true),("Ar_Flow","Ar",true),
                ("O2_Flow","O2",true),("APC_Pressure","APC Pre",true),
                ("APC_Position","APC Pos",true),("VVC1","VVC1",true),
                ("VVC2","VVC2",true),("VVC3","VVC3",true),
                ("Proc_Status","Proc Status",true)
            };
            foreach (var (n, h, ro) in cols)
                g.Columns.Add(new DataGridViewTextBoxColumn
                { Name = n, HeaderText = h, ReadOnly = ro, SortMode = DataGridViewColumnSortMode.Automatic });
            return g;
        }

        void RefreshAll()
        {
            RefreshGrid(); RefreshStats();
            // [CHG] 체크된 모든 데이터셋을 함께 넘겨서 스미스차트에 겹쳐 그리게 함
            var datasets = (_chkOverlay != null && !_chkOverlay.Checked)
                ? ((_ds != null)
                    ? new List<(int idx, MeasurementDataset ds)> { (_activeDsIndex, _ds) }
                    : new List<(int idx, MeasurementDataset ds)>())
                : GetOverlaySelection();

            _chart.SetDatasets(datasets, _cbColor?.SelectedIndex ?? 0);
        }

        void RefreshGrid()
        {
            _grid.Rows.Clear();
            if (_ds == null) return;
            foreach (var s in _ds.Steps)
            {
                _grid.Rows.Add(
                    s.Step, s.Vout_Vrms.ToString("F4"), s.Iout_Arms.ToString("F4"),
                    s.Phase_deg.ToString("F2"), s.R.ToString("F4"), s.X.ToString("F4"),
                    s.Gamma_Real.ToString("F6"), s.Gamma_Imag.ToString("F6"),
                    s.GammaMag.ToString("F6"), s.VSWR.ToString("F3"),
                    s.Z_Text, s.Z_Normalized,
                    s.ForwardP_W.ToString("F4"), s.ReflectedP_W.ToString("F4"),
                    s.DeliveredP_W.ToString("F4"), s.ReturnLoss_dB.ToString("F2"),
                    s.Efficiency_pct.ToString("F1"),s.Ar_Flow.ToString("F1"), s.O2_Flow.ToString("F1"),
                    s.APC_Pressure.ToString("F2"), s.APC_Position.ToString("F2"), s.VVC1.ToString("F2"), s.VVC2.ToString("F2"), s.VVC3.ToString("F2"),s.Proc_Status
                );
                var row = _grid.Rows[_grid.Rows.Count - 1];
                Color vc = s.VSWR < 1.5
                    ? Color.FromArgb(20, 0, 180, 0)
                    : s.VSWR < 2.5 ? Color.FromArgb(20, 220, 180, 0)
                    : Color.FromArgb(20, 220, 0, 0);
                row.Cells[9].Style.BackColor = vc;
            }
        }

        void RefreshStats()
        {
            if (_ds == null || !_ds.Steps.Any()) { _statLbl.Text = ""; return; }
            var b = _ds.BestVSWR; var w = _ds.WorstVSWR;
            _statLbl.Text = $"스텝 {_ds.Steps.Count}개  |  " +
                $"최적 VSWR: {b?.VSWR:F3} (S{b?.Step})  |  " +
                $"최악: {w?.VSWR:F3} (S{w?.Step})  |  " +
                $"평균 VSWR: {_ds.AvgVSWR:F3}  |  평균 효율: {_ds.AvgEfficiency:F1}%";
        }

        void HighlightRow(int idx)
        {
            if (idx < 0 || idx >= _grid.Rows.Count) return;

            _isUpdatingSelection = true;
            try
            {
                _grid.ClearSelection();
                _grid.Rows[idx].Selected = true;
                if (idx >= 0 && idx < _grid.Rows.Count)
                    _grid.FirstDisplayedScrollingRowIndex = idx;
            }
            finally
            {
                _isUpdatingSelection = false;
            }
        }

        void Grid_CellEndEdit(object s, DataGridViewCellEventArgs e)
        {
            if (_ds == null || e.RowIndex >= _ds.Steps.Count) return;
            var ms = _ds.Steps[e.RowIndex];
            var val = _grid.Rows[e.RowIndex].Cells[e.ColumnIndex].Value?.ToString();
            if (!double.TryParse(val, out double d)) return;
            switch (_grid.Columns[e.ColumnIndex].Name)
            {
                case "Vout_Vrms": ms.Vout_Vrms = d; ms.ComputeFromVI(_ds.Z0); break;
                case "Iout_Arms": ms.Iout_Arms = d; ms.ComputeFromVI(_ds.Z0); break;
                case "Phase_deg": ms.Phase_deg = d; ms.ComputeFromVI(_ds.Z0); break;
                case "R": ms.R = d; ms.ComputeFromZ(_ds.Z0); break;
                case "X": ms.X = d; ms.ComputeFromZ(_ds.Z0); break;
                case "ForwardP_W":
                    ms.ForwardP_W = d;
                    ms.ReflectedP_W = ms.ForwardP_W * ms.GammaMag * ms.GammaMag; break;
                case "DeliveredP_W": ms.DeliveredP_W = d; break;
                case "Ar_Flow": ms.Ar_Flow = d; break;
                case "O2_Flow": ms.O2_Flow = d; break;
                case "APC_Pressure": ms.APC_Pressure = d; break;
                case "APC_Position": ms.APC_Position = d; break;
                case "VVC1": ms.VVC1 = d; break;
                case "VVC2": ms.VVC2 = d; break;
                case "VVC3": ms.VVC3 = d; break;
                //case "Proc_Status": ms.Proc_Status = d; break;
            }
            RefreshAll();
        }

        void AddManual()
        {
            using var dlg = new ManualStepDialog(_ds?.Z0 ?? 50);
            if (dlg.ShowDialog() != DialogResult.OK) return;

            if (_ds == null)
            {
                _dsList.Add(new MeasurementDataset { Z0 = 50 });
                _activeDsIndex = _dsList.Count - 1;
                if (!_selectedDsIndices.Contains(_activeDsIndex)) _selectedDsIndices.Add(_activeDsIndex);
                RefreshDatasetList();
            }
            _ds.Steps.Add(dlg.Result);
            RefreshAll();
        }

        public void DeleteSelected()
        {
            if (_ds == null || _grid.SelectedRows.Count == 0) return;
            int idx = _grid.SelectedRows[0].Index;
            if (idx >= 0 && idx < _ds.Steps.Count) _ds.Steps.RemoveAt(idx);
            RefreshAll();
        }
    }

    // ── 차트 드로잉 패널 (측정 데이터용) ──
    // [CHG] 단일 MeasurementDataset → 여러 개를 겹쳐서(overlay) 그릴 수 있도록 변경
    public class MeasurementChartPanel : Control
    {
        // [ADD] 데이터셋별 구분 색상 팔레트 (뷰어 패널의 체크박스 글자색과도 공용으로 사용)
        public static readonly Color[] DatasetPalette =
        {
            Color.FromArgb(214, 69, 65),   // 빨강
            Color.FromArgb(48, 120, 200),  // 파랑
            Color.FromArgb(60, 170, 90),   // 초록
            Color.FromArgb(180, 90, 180),  // 보라
            Color.FromArgb(210, 160, 40),  // 금색
            Color.FromArgb(40, 175, 175),  // 청록
        };

        private class Overlay
        {
            public int DsIndex;
            public MeasurementDataset Ds;
            public Color Color;
            public string Name;
        }

        private List<Overlay> _overlays = new List<Overlay>();
        private int _colorMode = 0;
        private int _hlDsIdx = -1;   // [CHG] 하이라이트 대상 (데이터셋 인덱스, 스텝 인덱스)
        private int _hlStepIdx = -1;
        public event Action<int, int> StepHovered;   // (dsIndex, stepIndex), 해제 시 (-1,-1)

        public MeasurementChartPanel()
        {
            DoubleBuffered = true; ResizeRedraw = true;
            SetStyle(ControlStyles.OptimizedDoubleBuffer |
                     ControlStyles.AllPaintingInWmPaint | ControlStyles.UserPaint, true);
        }

        // [CHG] (데이터셋 인덱스, 데이터셋) 목록을 받아 모두 겹쳐서 표시
        public void SetDatasets(List<(int idx, MeasurementDataset ds)> datasets, int colorMode)
        {
            _overlays = datasets.Select((d, i) => new Overlay
            {
                DsIndex = d.idx,
                Ds = d.ds,
                Color = DatasetPalette[i % DatasetPalette.Length],
                Name = string.IsNullOrEmpty(d.ds.Name) ? $"Dataset{d.idx + 1}" : d.ds.Name
            }).ToList();
            _colorMode = colorMode;
            Invalidate();
        }

        public void SetColorMode(int m) { _colorMode = m; Invalidate(); }

        // [CHG] 어느 데이터셋의 몇 번째 스텝인지 함께 지정
        public void Highlight(int dsIndex, int stepIndex)
        {
            _hlDsIdx = dsIndex; _hlStepIdx = stepIndex; Invalidate();
        }

        PointF Sp(double re, double im, float cx, float cy, float r)
            => new PointF(cx + (float)(re * r), cy - (float)(im * r));

        void ClipDraw(Graphics g, float cx, float cy, float rad, Action act)
        {
            var st = g.Save();
            var gp = new GraphicsPath(); gp.AddEllipse(cx - rad, cy - rad, rad * 2, rad * 2);
            g.SetClip(gp); act(); g.Restore(st);
        }

        // [CHG] 특정 데이터셋(ds) 기준으로 색상 계산 (여러 데이터셋이 겹쳐도 각자 자기 데이터 범위로 계산)
        Color PtColor(MeasurementDataset ds, MeasurementStep s, int idx)
        {
            if (_colorMode == 1)
            {
                var pal = new[]{Color.OrangeRed,Color.SteelBlue,Color.SeaGreen,
                              Color.DarkOrchid,Color.Crimson,Color.Teal};
                return pal[idx % pal.Length];
            }
            if (_colorMode == 2 && ds != null)
            {
                double maxP = ds.Steps.Max(x => x.ForwardP_W); if (maxP < 1) maxP = 1;
                double t = s.ForwardP_W / maxP;
                return Color.FromArgb((int)(50 + 205 * t), 80, (int)(220 * (1 - t)));
            }
            // VSWR 열지도
            if (ds == null) return Color.Gray;
            double minV = ds.Steps.Min(x => x.VSWR), maxV = ds.Steps.Max(x => x.VSWR);
            double tv = maxV > minV ? (s.VSWR - minV) / (maxV - minV) : 0;
            tv = Math.Max(0, Math.Min(1, tv));
            return Color.FromArgb((int)(255 * Math.Min(tv * 2, 1)), (int)(255 * Math.Min((1 - tv) * 2, 1)), 0);
        }

        protected override void OnPaint(PaintEventArgs e)
        {
            base.OnPaint(e);
            var g = e.Graphics;
            g.SmoothingMode = SmoothingMode.AntiAlias;
            g.TextRenderingHint = TextRenderingHint.ClearTypeGridFit;
            float cx = Width / 2f, cy = Height / 2f, rad = Math.Min(cx, cy) - 36;
            DrawGrid(g, cx, cy, rad);
            // [CHG] 체크된 모든 데이터셋을 순서대로 겹쳐 그림
            //foreach (var ov in _overlays)
            //    if (ov.Ds != null && ov.Ds.Steps.Any())
            //        DrawData(g, cx, cy, rad, ov);
            DrawLegend(g);   // [ADD] 2개 이상 겹칠 때 데이터셋 범례 표시

            // [CHG] 체크된 모든 데이터셋을 순서대로 겹쳐 그림
            foreach (var ov in _overlays)
                if (ov.Ds != null && ov.Ds.Steps.Any())
                    DrawData(g, cx, cy, rad, ov);

            var hovered = _overlays.FirstOrDefault(x => x.DsIndex == _hlDsIdx);
            if (hovered != null && hovered.Ds != null && _hlStepIdx >= 0 && _hlStepIdx < hovered.Ds.Steps.Count)
            {
                var s = hovered.Ds.Steps[_hlStepIdx];
                if (s.GammaMag <= 1.05)
                {
                    var sp = Sp(s.Gamma_Real, s.Gamma_Imag, cx, cy, rad);
                    DrawTooltip(g, hovered, s, sp);
                }
            }
        }

        void DrawGrid(Graphics g, float cx, float cy, float rad)
        {
            g.FillEllipse(new SolidBrush(Color.FromArgb(245, 248, 255)), cx - rad, cy - rad, rad * 2, rad * 2);
            foreach (double mag in new[] { 0.25, 0.5, 0.75 })
            {
                float r2 = (float)(mag * rad);
                ClipDraw(g, cx, cy, rad, () => {
                    using var p = new Pen(Color.FromArgb(45, 83, 74, 183), .5f) { DashStyle = DashStyle.Dash };
                    g.DrawEllipse(p, cx - r2, cy - r2, r2 * 2, r2 * 2);
                });
                g.DrawString(((1 + mag) / (1 - mag)).ToString("F1"), new Font("Arial", 7f),
                    new SolidBrush(Color.FromArgb(100, 83, 74, 183)), cx + r2 + 2, cy - 7);
            }
            foreach (double rn in new[] { 0.0, 0.5, 1.0, 2.0 })
            {
                float cr = (float)(1.0 / (1 + rn) * rad), ccx = cx + (float)(rn / (1 + rn) * rad);
                bool st = rn == 0 || rn == 1;
                ClipDraw(g, cx, cy, rad, () => {
                    using var p = new Pen(Color.FromArgb(st ? 130 : 50, 24, 95, 165), st ? .9f : .5f);
                    g.DrawEllipse(p, ccx - cr, cy - cr, cr * 2, cr * 2);
                });
            }
            foreach (double xn in new[] { 0.5, 1.0, 2.0 })
                foreach (int sign in new[] { 1, -1 })
                {
                    double xnv = sign * xn;
                    float acx = cx + rad, acy = cy - (float)(1.0 / xnv * rad), ar = (float)(Math.Abs(1.0 / xnv) * rad);
                    bool st = xn == 1.0;
                    ClipDraw(g, cx, cy, rad, () => {
                        using var p = new Pen(Color.FromArgb(st ? 120 : 45, 133, 79, 11), st ? .9f : .5f);
                        g.DrawEllipse(p, acx - ar, acy - ar, ar * 2, ar * 2);
                    });
                }
            g.DrawLine(new Pen(Color.FromArgb(70, 80, 80, 80), .8f), cx - rad, cy, cx + rad, cy);
            g.DrawEllipse(new Pen(Color.FromArgb(140, 80, 80, 80), 1.2f), cx - rad, cy - rad, rad * 2, rad * 2);

            DrawAxis(g, cx, cy, rad);

            var lf = new Font("Arial", 7.5f); var lb = new SolidBrush(Color.FromArgb(120, 90, 90, 90));
            g.DrawString("SC", lf, lb, cx - rad - 20, cy - 6);
            g.DrawString("OC", lf, lb, cx + rad + 3, cy - 6);
            g.DrawString("Z₀", lf, lb, cx - 8, cy - 14);
            g.FillEllipse(lb, cx - 2.5f, cy - 2.5f, 5, 5);
        }

        // [CHG] 특정 overlay(데이터셋 1개분)를 그리는 메서드로 변경 – 여러 번 호출되어 겹쳐진다
        void DrawData(Graphics g, float cx, float cy, float rad, Overlay ov)
        {
            var ds = ov.Ds;

            var valid = ds.Steps.Where(s => s.GammaMag <= 1.05).ToList();
            if (valid.Count >= 2)
            {
                var pts = valid.Select(s => Sp(s.Gamma_Real, s.Gamma_Imag, cx, cy, rad)).ToArray();
                using var tp = new Pen(Color.FromArgb(60, ov.Color), 1f) { DashStyle = DashStyle.Dot };
                g.DrawLines(tp, pts);
            }

            var trace = ds.Steps.Where(s => s.GammaMag <= 1.05 && s.Step >= 1 && s.Step <= ds.Steps.Count)
                                  .OrderBy(s => s.Step)
                                  .ToList();
            if (trace.Count >= 2)
            {
                var pts = trace.Select(s => Sp(s.Gamma_Real, s.Gamma_Imag, cx, cy, rad)).ToArray();
                using var tp = new Pen(ov.Color, 1.6f) { DashStyle = DashStyle.Dash };
                g.DrawLines(tp, pts);
            }

            for (int i = 0; i < ds.Steps.Count; i++)
            {
                var s = ds.Steps[i];
                if (s.GammaMag > 1.05) continue;
                var sp = Sp(s.Gamma_Real, s.Gamma_Imag, cx, cy, rad);
                bool hl = (ov.DsIndex == _hlDsIdx && i == _hlStepIdx);
                float sz = hl ? 9f : 6f;

                g.FillEllipse(Brushes.White, sp.X - sz - 1.5f, sp.Y - sz - 1.5f, (sz + 1.5f) * 2, (sz + 1.5f) * 2);

                Color fillColor = (_overlays.Count > 1) ? ov.Color : PtColor(ds, s, i+1);

                using var br = new SolidBrush(fillColor);
                g.FillEllipse(br, sp.X - sz, sp.Y - sz, sz * 2, sz * 2);
                // [ADD] 어느 데이터셋 포인트인지 구분되도록 데이터셋 색상 테두리를 항상 표시
                using var ring = new Pen(ov.Color, hl ? 2f : 1.2f);
                g.DrawEllipse(ring, sp.X - sz, sp.Y - sz, sz * 2, sz * 2);
                if (hl) g.DrawEllipse(new Pen(Color.Black, 1.5f), sp.X - sz - 2, sp.Y - sz - 2, (sz + 2) * 2, (sz + 2) * 2);

                g.DrawString(s.Step.ToString(), new Font("Arial", 7f, FontStyle.Bold),
                    new SolidBrush(ov.Color), sp.X + sz + 2, sp.Y - 4);
            }
        }

        // [ADD] 2개 이상의 데이터셋이 겹쳐 표시될 때 좌상단에 범례 표시
        void DrawLegend(Graphics g)
        {
            if (_overlays.Count <= 1) return;
            float x = 8, y = 8;
            var f = new Font("Arial", 7.5f, FontStyle.Bold);
            foreach (var ov in _overlays)
            {
                g.FillRectangle(new SolidBrush(ov.Color), x, y, 10, 10);
                g.DrawRectangle(Pens.Gray, x, y, 10, 10);
                g.DrawString(ov.Name, f, Brushes.Black, x + 14, y - 1);
                y += 15;
            }
        }

        void DrawTooltip(Graphics g, Overlay ov, MeasurementStep s, PointF sp)
        {
            string[] lines =
            {
                $"[{ov.Name}]",
                $"Step {s.Step}",
                $"Z = {s.Z_Text}",
                $"|Γ| = {s.GammaMag:F4}",
                $"VSWR = {s.VSWR:F3}",
                $"RL = {s.ReturnLoss_dB:F1} dB",
                $"V = {s.Vout_Vrms:F3} Vrms",
                $"I = {s.Iout_Arms:F3} Arms",
                $"θ = {s.Phase_deg:F1}°",
                $"Fwd = {s.ForwardP_W:F2} W",
                $"Del = {s.DeliveredP_W:F2} W",
                $"η = {s.Efficiency_pct:F1}%",
                $"Reflected = {s.ReflectedP_W:F1} W",
                $"ArFlow = {s.Ar_Flow:F2} sccm",
                $"O2Flow = {s.O2_Flow:F2} sccm",
                $"APC Pressure = {s.APC_Pressure:F2} Torr",
                $"APC Position = {s.APC_Position:F2} %",
                $"VVC1 = {s.VVC1:F2} pF",
                $"VVC2 = {s.VVC2:F2} pF",
                $"VVC3 = {s.VVC3:F2} pF"
            };
            var f = new Font("Consolas", 7.5f);
            float fw = lines.Max(l => g.MeasureString(l, f).Width) + 10, fh = lines.Length * 13f + 8;
            float tx = sp.X + 12, ty = sp.Y - fh / 2;
            ty = sp.Y - fh - 12;
            if (tx + fw > Width) tx = sp.X - fw - 12;
            if (ty < 4) ty = sp.Y + 12;
            if (ty + fh > Height) ty = Height - fh - 4;
            g.FillRectangle(new SolidBrush(Color.FromArgb(240, 245, 255, 255)), tx, ty, fw, fh);
            g.DrawRectangle(new Pen(ov.Color), tx, ty, fw, fh);
            for (int li = 0; li < lines.Length; li++)
                g.DrawString(lines[li], f, Brushes.Black, tx + 5, ty + 4 + li * 13);
        }

        public void SaveToPng(string path, int w, int h)
        {
            using var bmp = new Bitmap(w, h);
            using var g = Graphics.FromImage(bmp);
            g.SmoothingMode = SmoothingMode.AntiAlias;
            g.Clear(Color.White);
            float cx = w / 2f, cy = h / 2f, rad = Math.Min(cx, cy) - 50;
            DrawGrid(g, cx, cy, rad);
           // foreach (var ov in _overlays)
           //     if (ov.Ds != null && ov.Ds.Steps.Any())
           //         DrawData(g, cx, cy, rad, ov);
            DrawLegend(g);
            foreach (var ov in _overlays)
                if (ov.Ds != null && ov.Ds.Steps.Any())
                    DrawData(g, cx, cy, rad, ov);
            bmp.Save(path, System.Drawing.Imaging.ImageFormat.Png);
        }

        // [CHG] 모든 overlay(데이터셋)의 포인트를 통틀어 가장 가까운 점을 찾음
        protected override void OnMouseMove(MouseEventArgs e)
        {
            base.OnMouseMove(e);
            if (_overlays.Count == 0) return;
            float cx = Width / 2f, cy = Height / 2f, rad = Math.Min(cx, cy) - 36;
            int bestDs = -1, bestStep = -1; double bestD = 16 * 16;
            foreach (var ov in _overlays)
            {
                for (int i = 0; i < ov.Ds.Steps.Count; i++)
                {
                    var s = ov.Ds.Steps[i];
                    var sp = Sp(s.Gamma_Real, s.Gamma_Imag, cx, cy, rad);
                    double d = (e.X - sp.X) * (e.X - sp.X) + (e.Y - sp.Y) * (e.Y - sp.Y);
                    if (d < bestD) { bestD = d; bestDs = ov.DsIndex; bestStep = i; }
                }
            }
            if (bestDs != _hlDsIdx || bestStep != _hlStepIdx)
            {
                _hlDsIdx = bestDs; _hlStepIdx = bestStep;
                StepHovered?.Invoke(bestDs, bestStep);
                Invalidate();
            }
            Cursor = bestDs >= 0 ? Cursors.Hand : Cursors.Default;
        }

        protected override void OnMouseLeave(EventArgs e)
        {
            base.OnMouseLeave(e);
            if (_hlDsIdx >= 0 || _hlStepIdx >= 0) { _hlDsIdx = -1; _hlStepIdx = -1; StepHovered?.Invoke(-1, -1); Invalidate(); }
        }

        void DrawAxis(Graphics g, float cx, float cy, float rad)
        {
            float ext = rad * 1.15f;
            using var axisPen = new Pen(Color.FromArgb(150, 90, 90, 90), 1f);
            var f = new Font("Arial", 8f);
            var br = new SolidBrush(Color.FromArgb(150, 60, 60, 60));

            g.DrawLine(axisPen, cx - ext, cy, cx + ext, cy);
            g.DrawLine(axisPen, cx, cy - ext, cx, cy + ext);

            double[] ticks = { -1.0, -0.5, 0.0, 0.5, 1.0 };
            foreach (double t in ticks)
            {
                float tx = cx + (float)(t * rad);
                float ty = cy - (float)(t * rad);

                g.DrawLine(axisPen, tx, cy - 4, tx, cy + 4);
                g.DrawString(t.ToString("0.0"), f, br, tx - 10, cy + 6);

                if (t != 0.0)
                {
                    g.DrawLine(axisPen, cx - 4, ty, cx + 4, ty);
                    g.DrawString(t.ToString("0.0"), f, br, cx + 6, ty - 6);
                }
            }
        }
    }

    // ── 수동 스텝 입력 다이얼로그 ──
    public class ManualStepDialog : Form
    {
        private NumericUpDown _nStep, _nVout, _nIout, _nPhase, _nR, _nX, _nFwd;
        private RadioButton _rbVI, _rbRX;
        private double _z0;
        public MeasurementStep Result { get; private set; }

        public ManualStepDialog(double z0 = 50)
        {
            _z0 = z0; Text = "스텝 수동 입력";
            Size = new Size(340, 380); FormBorderStyle = FormBorderStyle.FixedDialog;
            StartPosition = FormStartPosition.CenterParent;

            var t = new TableLayoutPanel { Dock = DockStyle.Fill, ColumnCount = 2, Padding = new Padding(10) };
            t.ColumnStyles.Add(new ColumnStyle(SizeType.Percent, 45));
            t.ColumnStyles.Add(new ColumnStyle(SizeType.Percent, 55));

            _rbVI = new RadioButton { Text = "V/I/θ", Checked = true };
            _rbRX = new RadioButton { Text = "R/X 직접" };
            t.Controls.Add(_rbVI, 0, 0); t.Controls.Add(_rbRX, 1, 0);

            NumericUpDown N(decimal mn, decimal mx, decimal v, int d = 4)
                => new NumericUpDown { Minimum = mn, Maximum = mx, Value = v, DecimalPlaces = d, Dock = DockStyle.Fill };

            void Row(string lbl, Control c)
            {
                t.Controls.Add(new Label
                {
                    Text = lbl,
                    Dock = DockStyle.Fill,
                    TextAlign = ContentAlignment.MiddleRight
                }, 0, t.RowCount);
                t.Controls.Add(c, 1, t.RowCount - 1);
            }

            _nStep = N(1, 9999, 1, 0); Row("Step", _nStep);
            _nVout = N(0, 10000, 10); Row("Vout Vrms", _nVout);
            _nIout = N(0, 10000, .2M); Row("Iout Arms", _nIout);
            _nPhase = N(-180, 180, 0, 2); Row("θ deg", _nPhase);
            _nR = N(0, 100000, 75); Row("R Ω", _nR);
            _nX = N(-100000, 100000, 50); Row("X Ω", _nX);
            _nFwd = N(0, 1000000, 0); Row("Fwd P W", _nFwd);

            var ok = new Button { Text = "추가", DialogResult = DialogResult.OK, Dock = DockStyle.Bottom };
            ok.Click += (s, e) => Build();
            t.SetColumnSpan(ok, 2); t.Controls.Add(ok, 0, t.RowCount);

            Controls.Add(t);
        }

        void Build()
        {
            Result = new MeasurementStep
            {
                Step = (int)_nStep.Value,
                Vout_Vrms = (double)_nVout.Value,
                Iout_Arms = (double)_nIout.Value,
                Phase_deg = (double)_nPhase.Value,
                ForwardP_W = (double)_nFwd.Value
            };
            if (_rbRX.Checked) { Result.R = (double)_nR.Value; Result.X = (double)_nX.Value; Result.ComputeFromZ(_z0); }
            else Result.ComputeFromVI(_z0);
        }
    }
}
