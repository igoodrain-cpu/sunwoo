namespace Iruza.src.Parameter
{
    partial class ParameterForm
    {
        /// <summary>
        /// Required designer variable.
        /// </summary>
        private System.ComponentModel.IContainer components = null;

        /// <summary>
        /// Clean up any resources being used.
        /// </summary>
        /// <param name="disposing">true if managed resources should be disposed; otherwise, false.</param>
        protected override void Dispose(bool disposing)
        {
            if (disposing && (components != null))
            {
                components.Dispose();
            }
            base.Dispose(disposing);
        }

        #region Windows Form Designer generated code

        /// <summary>
        /// Required method for Designer support - do not modify
        /// the contents of this method with the code editor.
        /// </summary>
        private void InitializeComponent()
        {
            this.lblStartTime = new System.Windows.Forms.Label();
            this.lblEndTime = new System.Windows.Forms.Label();
            this.dtpStartTime = new System.Windows.Forms.DateTimePicker();
            this.dtpEndTime = new System.Windows.Forms.DateTimePicker();
            this.btnSave = new System.Windows.Forms.Button();
            this.btnSearch = new System.Windows.Forms.Button();
            this.btnReset = new System.Windows.Forms.Button();
            this.gbSearch = new System.Windows.Forms.GroupBox();
            this.gbCondition = new System.Windows.Forms.GroupBox();
            this.lblRecipeName = new System.Windows.Forms.Label();
            this.txtRecipeName = new System.Windows.Forms.TextBox();
            this.lblStep = new System.Windows.Forms.Label();
            this.cboStep = new System.Windows.Forms.ComboBox();
            this.lblPower = new System.Windows.Forms.Label();
            this.txtMinPower = new System.Windows.Forms.TextBox();
            this.lblPowerTilde = new System.Windows.Forms.Label();
            this.txtMaxPower = new System.Windows.Forms.TextBox();
            this.gbSelect = new System.Windows.Forms.GroupBox();
            this.radioOutputSn = new System.Windows.Forms.RadioButton();
            this.radioInputSn = new System.Windows.Forms.RadioButton();
            this.gbSearch.SuspendLayout();
            this.gbCondition.SuspendLayout();
            this.gbSelect.SuspendLayout();
            this.SuspendLayout();
            // 
            // lblStartTime
            // 
            this.lblStartTime.AutoSize = true;
            this.lblStartTime.Location = new System.Drawing.Point(20, 30);
            this.lblStartTime.Name = "lblStartTime";
            this.lblStartTime.Size = new System.Drawing.Size(63, 12);
            this.lblStartTime.TabIndex = 0;
            this.lblStartTime.Text = "Start Time";
            // 
            // lblEndTime
            // 
            this.lblEndTime.AutoSize = true;
            this.lblEndTime.Location = new System.Drawing.Point(20, 63);
            this.lblEndTime.Name = "lblEndTime";
            this.lblEndTime.Size = new System.Drawing.Size(60, 12);
            this.lblEndTime.TabIndex = 1;
            this.lblEndTime.Text = "End Time";
            // 
            // dtpStartTime
            // 
            this.dtpStartTime.CustomFormat = "yyyy-MM-dd HH:mm:ss";
            this.dtpStartTime.Format = System.Windows.Forms.DateTimePickerFormat.Custom;
            this.dtpStartTime.Location = new System.Drawing.Point(108, 24);
            this.dtpStartTime.Name = "dtpStartTime";
            this.dtpStartTime.Size = new System.Drawing.Size(221, 21);
            this.dtpStartTime.TabIndex = 2;
            // 
            // dtpEndTime
            // 
            this.dtpEndTime.CustomFormat = "yyyy-MM-dd HH:mm:ss";
            this.dtpEndTime.Format = System.Windows.Forms.DateTimePickerFormat.Custom;
            this.dtpEndTime.Location = new System.Drawing.Point(108, 57);
            this.dtpEndTime.Name = "dtpEndTime";
            this.dtpEndTime.Size = new System.Drawing.Size(221, 21);
            this.dtpEndTime.TabIndex = 3;
            // 
            // btnSave
            // 
            this.btnSave.Location = new System.Drawing.Point(298, 349);
            this.btnSave.Name = "btnSave";
            this.btnSave.Size = new System.Drawing.Size(75, 29);
            this.btnSave.TabIndex = 8;
            this.btnSave.Text = "저장";
            this.btnSave.UseVisualStyleBackColor = true;
            this.btnSave.Click += new System.EventHandler(this.btnSave_Click);
            // 
            // btnSearch
            // 
            this.btnSearch.Location = new System.Drawing.Point(208, 349);
            this.btnSearch.Name = "btnSearch";
            this.btnSearch.Size = new System.Drawing.Size(75, 29);
            this.btnSearch.TabIndex = 7;
            this.btnSearch.Text = "검색";
            this.btnSearch.TextImageRelation = System.Windows.Forms.TextImageRelation.TextAboveImage;
            this.btnSearch.UseVisualStyleBackColor = true;
            this.btnSearch.Click += new System.EventHandler(this.btnSearch_Click);
            // 
            // btnReset
            // 
            this.btnReset.Location = new System.Drawing.Point(12, 349);
            this.btnReset.Name = "btnReset";
            this.btnReset.Size = new System.Drawing.Size(75, 29);
            this.btnReset.TabIndex = 6;
            this.btnReset.Text = "초기화";
            this.btnReset.UseVisualStyleBackColor = true;
            this.btnReset.Click += new System.EventHandler(this.btnReset_Click);
            // 
            // gbSearch
            // 
            this.gbSearch.Controls.Add(this.dtpEndTime);
            this.gbSearch.Controls.Add(this.lblStartTime);
            this.gbSearch.Controls.Add(this.lblEndTime);
            this.gbSearch.Controls.Add(this.dtpStartTime);
            this.gbSearch.Location = new System.Drawing.Point(12, 148);
            this.gbSearch.Name = "gbSearch";
            this.gbSearch.Size = new System.Drawing.Size(361, 100);
            this.gbSearch.TabIndex = 5;
            this.gbSearch.TabStop = false;
            this.gbSearch.Text = "검색 기간";
            // 
            // gbCondition
            // 
            this.gbCondition.Controls.Add(this.lblRecipeName);
            this.gbCondition.Controls.Add(this.txtRecipeName);
            this.gbCondition.Controls.Add(this.lblStep);
            this.gbCondition.Controls.Add(this.cboStep);
            this.gbCondition.Controls.Add(this.lblPower);
            this.gbCondition.Controls.Add(this.txtMinPower);
            this.gbCondition.Controls.Add(this.lblPowerTilde);
            this.gbCondition.Controls.Add(this.txtMaxPower);
            this.gbCondition.Location = new System.Drawing.Point(12, 12);
            this.gbCondition.Name = "gbCondition";
            this.gbCondition.Size = new System.Drawing.Size(361, 128);
            this.gbCondition.TabIndex = 9;
            this.gbCondition.TabStop = false;
            this.gbCondition.Text = "검색 조건";
            // 
            // lblRecipeName
            // 
            this.lblRecipeName.AutoSize = true;
            this.lblRecipeName.Location = new System.Drawing.Point(20, 28);
            this.lblRecipeName.Name = "lblRecipeName";
            this.lblRecipeName.Size = new System.Drawing.Size(82, 12);
            this.lblRecipeName.TabIndex = 0;
            this.lblRecipeName.Text = "Recipe Name";
            // 
            // txtRecipeName
            // 
            this.txtRecipeName.BorderStyle = System.Windows.Forms.BorderStyle.FixedSingle;
            this.txtRecipeName.Location = new System.Drawing.Point(108, 22);
            this.txtRecipeName.Name = "txtRecipeName";
            this.txtRecipeName.Size = new System.Drawing.Size(221, 21);
            this.txtRecipeName.TabIndex = 1;
            // 
            // lblStep
            // 
            this.lblStep.AutoSize = true;
            this.lblStep.Location = new System.Drawing.Point(20, 61);
            this.lblStep.Name = "lblStep";
            this.lblStep.Size = new System.Drawing.Size(30, 12);
            this.lblStep.TabIndex = 2;
            this.lblStep.Text = "Step";
            // 
            // cboStep
            // 
            this.cboStep.DropDownStyle = System.Windows.Forms.ComboBoxStyle.DropDownList;
            this.cboStep.FormattingEnabled = true;
            this.cboStep.Items.AddRange(new object[] {
            "전체",
            "1",
            "2",
            "3",
            "4",
            "5",
            "6",
            "7",
            "8",
            "9",
            "10",
            "11",
            "12",
            "13",
            "14",
            "15",
            "16",
            "17",
            "18",
            "19",
            "20"});
            this.cboStep.Location = new System.Drawing.Point(108, 55);
            this.cboStep.Name = "cboStep";
            this.cboStep.Size = new System.Drawing.Size(90, 20);
            this.cboStep.TabIndex = 3;
            // 
            // lblPower
            // 
            this.lblPower.AutoSize = true;
            this.lblPower.Location = new System.Drawing.Point(20, 94);
            this.lblPower.Name = "lblPower";
            this.lblPower.Size = new System.Drawing.Size(65, 12);
            this.lblPower.TabIndex = 4;
            this.lblPower.Text = "Power (W)";
            // 
            // txtMinPower
            // 
            this.txtMinPower.BorderStyle = System.Windows.Forms.BorderStyle.FixedSingle;
            this.txtMinPower.Location = new System.Drawing.Point(108, 88);
            this.txtMinPower.Name = "txtMinPower";
            this.txtMinPower.Size = new System.Drawing.Size(80, 21);
            this.txtMinPower.TabIndex = 5;
            // 
            // lblPowerTilde
            // 
            this.lblPowerTilde.AutoSize = true;
            this.lblPowerTilde.Location = new System.Drawing.Point(194, 92);
            this.lblPowerTilde.Name = "lblPowerTilde";
            this.lblPowerTilde.Size = new System.Drawing.Size(14, 12);
            this.lblPowerTilde.TabIndex = 6;
            this.lblPowerTilde.Text = "~";
            // 
            // txtMaxPower
            // 
            this.txtMaxPower.BorderStyle = System.Windows.Forms.BorderStyle.FixedSingle;
            this.txtMaxPower.Location = new System.Drawing.Point(211, 88);
            this.txtMaxPower.Name = "txtMaxPower";
            this.txtMaxPower.Size = new System.Drawing.Size(80, 21);
            this.txtMaxPower.TabIndex = 7;
            // 
            // gbSelect
            // 
            this.gbSelect.Controls.Add(this.radioInputSn);
            this.gbSelect.Controls.Add(this.radioOutputSn);
            this.gbSelect.Location = new System.Drawing.Point(12, 254);
            this.gbSelect.Name = "gbSelect";
            this.gbSelect.Size = new System.Drawing.Size(361, 71);
            this.gbSelect.TabIndex = 5;
            this.gbSelect.TabStop = false;
            this.gbSelect.Text = "선택";
            // 
            // radioOutputSn
            // 
            this.radioOutputSn.AutoSize = true;
            this.radioOutputSn.Location = new System.Drawing.Point(193, 31);
            this.radioOutputSn.Name = "radioOutputSn";
            this.radioOutputSn.Size = new System.Drawing.Size(102, 16);
            this.radioOutputSn.TabIndex = 0;
            this.radioOutputSn.TabStop = true;
            this.radioOutputSn.Text = "Output sensor";
            this.radioOutputSn.UseVisualStyleBackColor = true;
            // 
            // radioInputSn
            // 
            this.radioInputSn.AutoSize = true;
            this.radioInputSn.Location = new System.Drawing.Point(22, 31);
            this.radioInputSn.Name = "radioInputSn";
            this.radioInputSn.Size = new System.Drawing.Size(93, 16);
            this.radioInputSn.TabIndex = 0;
            this.radioInputSn.TabStop = true;
            this.radioInputSn.Text = "Input sensor";
            this.radioInputSn.UseVisualStyleBackColor = true;
            // 
            // ParameterForm
            // 
            this.AutoScaleDimensions = new System.Drawing.SizeF(7F, 12F);
            this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Font;
            this.ClientSize = new System.Drawing.Size(392, 402);
            this.Controls.Add(this.gbCondition);
            this.Controls.Add(this.gbSelect);
            this.Controls.Add(this.gbSearch);
            this.Controls.Add(this.btnReset);
            this.Controls.Add(this.btnSearch);
            this.Controls.Add(this.btnSave);
            this.FormBorderStyle = System.Windows.Forms.FormBorderStyle.FixedDialog;
            this.MaximizeBox = false;
            this.MinimizeBox = false;
            this.Name = "ParameterForm";
            this.StartPosition = System.Windows.Forms.FormStartPosition.CenterParent;
            this.Text = "Parameter";
            this.Load += new System.EventHandler(this.ParameterForm_Load);
            this.gbSearch.ResumeLayout(false);
            this.gbSearch.PerformLayout();
            this.gbCondition.ResumeLayout(false);
            this.gbCondition.PerformLayout();
            this.gbSelect.ResumeLayout(false);
            this.gbSelect.PerformLayout();
            this.ResumeLayout(false);

        }

        #endregion

        private System.Windows.Forms.Label lblStartTime;
        private System.Windows.Forms.Label lblEndTime;
        private System.Windows.Forms.DateTimePicker dtpStartTime;
        private System.Windows.Forms.DateTimePicker dtpEndTime;
        private System.Windows.Forms.Button btnSave;
        private System.Windows.Forms.Button btnSearch;
        private System.Windows.Forms.Button btnReset;
        private System.Windows.Forms.GroupBox gbSearch;
        private System.Windows.Forms.GroupBox gbCondition;
        private System.Windows.Forms.Label lblRecipeName;
        private System.Windows.Forms.TextBox txtRecipeName;
        private System.Windows.Forms.Label lblStep;
        private System.Windows.Forms.ComboBox cboStep;
        private System.Windows.Forms.Label lblPower;
        private System.Windows.Forms.TextBox txtMinPower;
        private System.Windows.Forms.Label lblPowerTilde;
        private System.Windows.Forms.GroupBox gbSelect;
        private System.Windows.Forms.RadioButton radioInputSn;
        private System.Windows.Forms.RadioButton radioOutputSn;
        private System.Windows.Forms.TextBox txtMaxPower;
    }
}
