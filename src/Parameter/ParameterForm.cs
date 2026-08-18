using System;
using System.IO;
using System.Windows.Forms;

namespace Iruza.src.Parameter
{
    public partial class ParameterForm : Form
    {
        private readonly string _parameterFilePath;
        private readonly TreeNode _treeNode;

        public ParameterForm(TreeNode treeNode)
        {
            InitializeComponent();
            this.StartPosition = FormStartPosition.CenterScreen;
            _parameterFilePath = Path.Combine(Application.StartupPath, "Parameter", "ParameterSetting.json");


            _treeNode = treeNode;
        }

        private void ParameterForm_Load(object sender, EventArgs e)
        {
            LoadParameterSetting();
        }

        private void btnSave_Click(object sender, EventArgs e)
        {
            var setting = new ParameterSetting
            {
                StartTime = dtpStartTime.Value,
                EndTime = dtpEndTime.Value
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
            }
            catch (FileNotFoundException)
            {
                dtpStartTime.Value = DateTime.Now.AddDays(-14);
                dtpEndTime.Value = DateTime.Now;
            }
            catch (Exception ex)
            {
                MessageBox.Show("파라미터 로드 중 오류가 발생했습니다.\n\n" + ex.Message,
                    "로드 오류", MessageBoxButtons.OK, MessageBoxIcon.Warning);

                dtpStartTime.Value = DateTime.Now.AddDays(-14);
                dtpEndTime.Value = DateTime.Now;
            }
        }

        private void btnSearch_Click(object sender, EventArgs e)
        {
            // PostgreSQL의 process_run 데이터를 트리 노드로 로드
            try
            {
                var startTime = dtpStartTime.Value;
                var endTime = dtpEndTime.Value;

                _treeNode.Nodes.Clear();


                // DB에서 데이터를 조회하여 트리 노드에 추가
                foreach (var runName in MeasurementDb.GetProcessRunNames(startTime, endTime))
                    _treeNode.Nodes.Add(new TreeNode(runName));

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
    }
}