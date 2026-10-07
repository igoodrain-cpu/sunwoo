// ════════════════════════════════════════════════════════════════
//  ParameterForm.cs  –  공정 실행 검색 조건 및 센서 선택 화면
//  만든이: 이선우
// ════════════════════════════════════════════════════════════════
using System;
using System.Globalization;
using System.IO;
using System.Windows.Forms;

namespace Iruza.src.Parameter
{
    /// <summary>
    /// 센서 선택 구분
    /// </summary>
    public enum SensorType
    {
        None = 0,
        Input = 1,
        Output = 2
    }
    // 검색 조건을 저장하거나 PostgreSQL 실행 이력을 트리 노드로 조회합니다.
    public partial class ParameterForm : Form
    {
        private readonly string _parameterFilePath;
        private readonly TreeNode _treeNode;

        /// <summary>
        /// 검색 성공 시점에 확정된 센서 선택값 (MainShell에서 읽음)
        /// </summary>
        public SensorType SelectedSensor { get; private set; } = SensorType.None;
        public ParameterForm(TreeNode treeNode, string recipeName, int stepNum, double minPower, double maxPower,
                     SensorType sensorType = SensorType.None)
        {
            InitializeComponent();
            this.StartPosition = FormStartPosition.CenterScreen;
            _parameterFilePath = Path.Combine(Application.StartupPath, "Parameter", "ParameterSetting.json");

            txtRecipeName.Text = recipeName;
            cboStep.SelectedIndex = stepNum > 0 ? cboStep.Items.IndexOf(stepNum.ToString(CultureInfo.InvariantCulture)) : 0;
            txtMinPower.Text = minPower.ToString(CultureInfo.InvariantCulture);
            txtMaxPower.Text = maxPower.ToString(CultureInfo.InvariantCulture);

            SetSensorType(sensorType);
            SelectedSensor = sensorType;

            _treeNode = treeNode;
        }

        private void ParameterForm_Load(object sender, EventArgs e)
        {
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
                MaxPower = condition.MaxPower,
                Sensor = condition.Sensor
            };

            setting.Save(_parameterFilePath);

            MessageBox.Show("파라미터가 저장되었습니다.", "저장 완료",
                MessageBoxButtons.OK, MessageBoxIcon.Information);

            //DialogResult = DialogResult.OK;
            //Close();
        }

        private void btnReset_Click(object sender, EventArgs e)
        {
            txtRecipeName.Text = string.Empty;
            cboStep.SelectedIndex = 0; // 전체
            txtMinPower.Text = string.Empty;
            txtMaxPower.Text = string.Empty;
            dtpStartTime.Value = DateTime.Now.AddDays(-14);
            dtpEndTime.Value = DateTime.Now;
            SetSensorType(SensorType.None);
        }

        // 저장된 JSON 검색 조건을 읽고, 파일이 없으면 기본 기간을 적용합니다.
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

                SetSensorType(setting.Sensor ?? SensorType.None);
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

        // 입력 조건을 검증한 뒤 검색된 실행 이름을 호출자가 제공한 트리에 채웁니다.
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

                // 검색 성공 시 센서 선택값 확정 후 OK 결과로 닫기
                SelectedSensor = condition.Sensor;
                DialogResult = DialogResult.OK;
                Close();
            }
            catch (Exception ex)
            {
                MessageBox.Show(
                    "PostgreSQL 연결 실패.\n\n" + ex.Message,
                    "DB 연결",
                    MessageBoxButtons.OK,
                    MessageBoxIcon.Warning);
            }
        }

        /// <summary>
        /// 현재 화면의 라디오 버튼 선택 상태를 반환합니다.
        /// </summary>
        public SensorType GetSensorType()
        {
            if (radioInputSn.Checked) return SensorType.Input;
            if (radioOutputSn.Checked) return SensorType.Output;
            return SensorType.None;
        }

        /// <summary>
        /// 라디오 버튼 선택 상태를 설정합니다.
        /// </summary>
        private void SetSensorType(SensorType sensorType)
        {
            radioInputSn.Checked = sensorType == SensorType.Input;
            radioOutputSn.Checked = sensorType == SensorType.Output;
        }

        /// <summary>
        /// 화면의 입력 컨트롤 값을 검색 조건으로 파싱합니다.
        /// Recipe Name / Step / Power 필드는 비어 있으면 제한 없음(null)으로 처리됩니다.
        /// </summary>
        private bool TryGetSearchCondition(out SearchCondition condition, out string errorMessage)
        {
            condition = new SearchCondition
            {
                StartTime = dtpStartTime.Value,
                EndTime = dtpEndTime.Value,
                Sensor = GetSensorType()
            };
            errorMessage = null;
            // 센서 선택 필수 (선택 사항으로 하려면 이 블록 삭제)
            if (condition.Sensor == SensorType.None)
            {
                errorMessage = "Input sensor 또는 Output sensor를 선택해 주세요.";
                return false;
            }

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

            public SensorType Sensor;
        }
    }
}
