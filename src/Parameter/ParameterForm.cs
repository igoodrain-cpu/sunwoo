using System;
using System.Globalization;
using System.IO;
using System.Windows.Forms;

namespace Iruza.src.Parameter
{
    public partial class ParameterForm : Form
    {
        private readonly string _parameterFilePath;
        private readonly TreeNode _treeNode;

        /*public ParameterForm(TreeNode treeNode)
        {
            InitializeComponent();
            this.StartPosition = FormStartPosition.CenterScreen;
            _parameterFilePath = Path.Combine(Application.StartupPath, "Parameter", "ParameterSetting.json");


            _treeNode = treeNode;
        }*/

        public ParameterForm()
        {
            InitializeComponent();
            InitializeChrome();
            this.StartPosition = FormStartPosition.CenterScreen;
            _parameterFilePath = Path.Combine(Application.StartupPath, "Parameter", "ParameterSetting.json");
        }

        public ParameterForm(TreeNode treeNode)
            : this()
        {
            _treeNode = treeNode;

            LoadParameterSetting();

            /*txtRecipeName.Text = recipeName;
            cboStep.SelectedIndex = stepNum > 0 ? cboStep.Items.IndexOf(stepNum.ToString(CultureInfo.InvariantCulture)) : 0;
            txtMinPower.Text = minPower.ToString(CultureInfo.InvariantCulture);
            txtMaxPower.Text = maxPower.ToString(CultureInfo.InvariantCulture);*/
        }

        private void ParameterForm_Load(object sender, EventArgs e)
        {
            if (IsInDesignMode())
            {
                return;
            }

            LoadParameterSetting();
        }

        private void btnSave_Click(object sender, EventArgs e)
        {
            if (!TryGetSearchCondition(out var condition, out var errorMessage))
            {
                MessageBox.Show(errorMessage, "입력 오류",
                    MessageBoxButtons.OK, MessageBoxIcon.Warning);
                return;
            }

            var setting = new ParameterSetting
            {
                StartTime = condition.StartTime,
                EndTime = condition.EndTime,
                RecipeName = condition.RecipeName,
                StepNum = condition.StepNum,
                MinPower = condition.MinPower,
                MaxPower = condition.MaxPower
            };

            setting.Save(_parameterFilePath);

            MessageBox.Show("파라미터가 저장되었습니다.", "저장 완료",
                MessageBoxButtons.OK, MessageBoxIcon.Information);

            //DialogResult = DialogResult.OK;
            //Close();
        }

        private void LoadParameterSetting()
        {
            try
            {
                var setting = ParameterSetting.Load(_parameterFilePath);

                dtpStartTime.Value = setting.StartTime ?? DateTime.Now.AddDays(-14);
                dtpEndTime.Value = setting.EndTime ?? DateTime.Now;
                txtRecipeName.Text = setting.RecipeName ?? string.Empty;
                cboStep.SelectedIndex = setting.StepNum.HasValue
                    ? cboStep.Items.IndexOf(setting.StepNum.Value.ToString(CultureInfo.InvariantCulture))
                    : 0;
                if (cboStep.SelectedIndex < 0)
                    cboStep.SelectedIndex = 0;
                txtMinPower.Text = setting.MinPower.HasValue
                    ? setting.MinPower.Value.ToString(CultureInfo.InvariantCulture)
                    : string.Empty;
                txtMaxPower.Text = setting.MaxPower.HasValue
                    ? setting.MaxPower.Value.ToString(CultureInfo.InvariantCulture)
                    : string.Empty;
            }
            catch (FileNotFoundException)
            {
                dtpStartTime.Value = DateTime.Now.AddDays(-14);
                dtpEndTime.Value = DateTime.Now;
                cboStep.SelectedIndex = 0;
            }
            catch (Exception ex)
            {
                MessageBox.Show("파라미터 로드 중 오류가 발생했습니다.\n\n" + ex.Message,
                    "로드 오류", MessageBoxButtons.OK, MessageBoxIcon.Warning);

                dtpStartTime.Value = DateTime.Now.AddDays(-14);
                dtpEndTime.Value = DateTime.Now;
                cboStep.SelectedIndex = 0;
            }
        }

        private void btnSearch_Click(object sender, EventArgs e)
        {
            if (!TryGetSearchCondition(out var condition, out var errorMessage))
            {
                MessageBox.Show(errorMessage, "입력 오류",
                    MessageBoxButtons.OK, MessageBoxIcon.Warning);
                return;
            }

            // PostgreSQL의 process_run 데이터를 트리 노드로 로드
            try
            {
                _treeNode.Nodes.Clear();

                // DB에서 조건에 맞는 run_name 목록을 조회하여 트리 노드에 추가
                foreach (var runName in MeasurementDb.SearchProcessRunNames(
                    condition.RecipeName,
                    condition.StepNum,
                    condition.MinPower,
                    condition.MaxPower,
                    condition.StartTime,
                    condition.EndTime))
                {
                    _treeNode.Nodes.Add(new TreeNode(runName));
                }

                // _treeNode.Nodes.Add(new TreeNode("test1"));
                // _treeNode.Nodes.Add(new TreeNode("test2"));

                Close();
            }
            catch (Exception ex)
            {


                MessageBox.Show(
                    "PostgreSQL 연결 실패. 샘플 데이터로 표시합니다.\n\n" + ex.Message,
                    "DB 연결",
                    MessageBoxButtons.OK,
                    MessageBoxIcon.Warning);
            }
        }

        private bool TryGetSearchCondition(out SearchCondition condition, out string errorMessage)
        {
            condition = new SearchCondition
            {
                StartTime = dtpStartTime.Value,
                EndTime = dtpEndTime.Value
            };
            errorMessage = null;

            if (condition.EndTime < condition.StartTime)
            {
                errorMessage = "End Time은 Start Time보다 빠를 수 없습니다.";
                return false;
            }

            condition.RecipeName = string.IsNullOrWhiteSpace(txtRecipeName.Text)
                ? null
                : txtRecipeName.Text.Trim();

            if (cboStep.SelectedIndex > 0 &&
                short.TryParse(cboStep.SelectedItem?.ToString(), NumberStyles.Integer,
                    CultureInfo.InvariantCulture, out var stepNum))
            {
                condition.StepNum = stepNum;
            }
            else
            {
                condition.StepNum = null;
            }

            if (!TryParseOptionalDecimal(txtMinPower.Text, out var minPower))
            {
                errorMessage = "Min Power 값이 올바르지 않습니다.";
                return false;
            }

            if (!TryParseOptionalDecimal(txtMaxPower.Text, out var maxPower))
            {
                errorMessage = "Max Power 값이 올바르지 않습니다.";
                return false;
            }

            if (minPower.HasValue && maxPower.HasValue && minPower.Value > maxPower.Value)
            {
                errorMessage = "Min Power는 Max Power보다 클 수 없습니다.";
                return false;
            }

            condition.MinPower = minPower;
            condition.MaxPower = maxPower;

            return true;
        }

        private static bool TryParseOptionalDecimal(string text, out decimal? value)
        {
            if (string.IsNullOrWhiteSpace(text))
            {
                value = null;
                return true;
            }

            if (decimal.TryParse(text, NumberStyles.Number, CultureInfo.InvariantCulture, out var d))
            {
                value = d;
                return true;
            }

            value = null;
            return false;
        }

        public short getStepNum()
        {
            if (cboStep.SelectedIndex > 0 &&
                short.TryParse(cboStep.SelectedItem?.ToString(), NumberStyles.Integer,
                    CultureInfo.InvariantCulture, out var stepNum))
            {
                return stepNum;
            }
            return 0;
        }

        public double getPowerMin()
        {
            if (double.TryParse(txtMinPower.Text, NumberStyles.Float,
                    CultureInfo.InvariantCulture, out var minPower))
            {
                return minPower;
            }
            return 0;
        }

        public double getPowerMax()
        {
            if (double.TryParse(txtMaxPower.Text, NumberStyles.Float,
                    CultureInfo.InvariantCulture, out var maxPower))
            {
                return maxPower;
            }
            return 0;
        }

        private struct SearchCondition
        {
            public string RecipeName;
            public short? StepNum;
            public decimal? MinPower;
            public decimal? MaxPower;
            public DateTime StartTime;
            public DateTime EndTime;
        }
    }
}