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
            this.pnlHeader = new System.Windows.Forms.Panel();
            this.btnClose = new System.Windows.Forms.Button();
            this.lblTitle = new System.Windows.Forms.Label();
            this.pnlSearchSection = new System.Windows.Forms.Panel();
            this.lblSearchSectionTitle = new System.Windows.Forms.Label();
            this.lblStartTime = new System.Windows.Forms.Label();
            this.lblEndTime = new System.Windows.Forms.Label();
            this.dtpStartTime = new System.Windows.Forms.DateTimePicker();
            this.dtpEndTime = new System.Windows.Forms.DateTimePicker();
            this.pnlConditionSection = new System.Windows.Forms.Panel();
            this.lblConditionSectionTitle = new System.Windows.Forms.Label();
            this.lblRecipeName = new System.Windows.Forms.Label();
            this.txtRecipeName = new System.Windows.Forms.TextBox();
            this.lblStep = new System.Windows.Forms.Label();
            this.cboStep = new System.Windows.Forms.ComboBox();
            this.lblPower = new System.Windows.Forms.Label();
            this.txtMinPower = new System.Windows.Forms.TextBox();
            this.lblPowerTilde = new System.Windows.Forms.Label();
            this.txtMaxPower = new System.Windows.Forms.TextBox();
            this.btnSave = new System.Windows.Forms.Button();
            this.btnSearch = new System.Windows.Forms.Button();
            this.pnlHeader.SuspendLayout();
            this.pnlSearchSection.SuspendLayout();
            this.pnlConditionSection.SuspendLayout();
            this.SuspendLayout();
            // 
            // pnlHeader
            // 
            this.pnlHeader.Anchor = ((System.Windows.Forms.AnchorStyles)(((System.Windows.Forms.AnchorStyles.Top | System.Windows.Forms.AnchorStyles.Left) 
            | System.Windows.Forms.AnchorStyles.Right)));
            this.pnlHeader.BackColor = System.Drawing.Color.White;
            this.pnlHeader.Controls.Add(this.btnClose);
            this.pnlHeader.Controls.Add(this.lblTitle);
            this.pnlHeader.Location = new System.Drawing.Point(1, 1);
            this.pnlHeader.Name = "pnlHeader";
            this.pnlHeader.Size = new System.Drawing.Size(464, 59);
            this.pnlHeader.TabIndex = 0;
            this.pnlHeader.MouseDown += new System.Windows.Forms.MouseEventHandler(this.pnlHeader_MouseDown);
            // 
            // btnClose
            // 
            this.btnClose.DialogResult = System.Windows.Forms.DialogResult.Cancel;
            this.btnClose.FlatAppearance.BorderSize = 0;
            this.btnClose.FlatAppearance.MouseDownBackColor = System.Drawing.Color.FromArgb(((int)(((byte)(245)))), ((int)(((byte)(247)))), ((int)(((byte)(251)))));
            this.btnClose.FlatAppearance.MouseOverBackColor = System.Drawing.Color.FromArgb(((int)(((byte)(245)))), ((int)(((byte)(247)))), ((int)(((byte)(251)))));
            this.btnClose.FlatStyle = System.Windows.Forms.FlatStyle.Flat;
            this.btnClose.Font = new System.Drawing.Font("Segoe UI", 12F, System.Drawing.FontStyle.Regular, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.btnClose.ForeColor = System.Drawing.Color.FromArgb(((int)(((byte)(110)))), ((int)(((byte)(122)))), ((int)(((byte)(143)))));
            this.btnClose.Location = new System.Drawing.Point(418, 12);
            this.btnClose.Name = "btnClose";
            this.btnClose.Size = new System.Drawing.Size(36, 36);
            this.btnClose.TabIndex = 1;
            this.btnClose.Text = "✕";
            this.btnClose.UseVisualStyleBackColor = true;
            this.btnClose.Click += new System.EventHandler(this.btnClose_Click);
            // 
            // lblTitle
            // 
            this.lblTitle.AutoSize = true;
            this.lblTitle.Font = new System.Drawing.Font("Segoe UI Semibold", 12F, System.Drawing.FontStyle.Bold, System.Drawing.GraphicsUnit.Point, ((byte)(0)));
            this.lblTitle.ForeColor = System.Drawing.Color.FromArgb(((int)(((byte)(31)))), ((int)(((byte)(41)))), ((int)(((byte)(55)))));
            this.lblTitle.Location = new System.Drawing.Point(24, 19);
            this.lblTitle.Name = "lblTitle";
            this.lblTitle.Size = new System.Drawing.Size(138, 21);
            this.lblTitle.TabIndex = 0;
            this.lblTitle.Text = "Parameter Search";
            this.lblTitle.MouseDown += new System.Windows.Forms.MouseEventHandler(this.pnlHeader_MouseDown);
            // 
            // pnlSearchSection
            // 
            this.pnlSearchSection.BackColor = System.Drawing.Color.White;
            this.pnlSearchSection.BorderStyle = System.Windows.Forms.BorderStyle.FixedSingle;
            this.pnlSearchSection.Controls.Add(this.lblSearchSectionTitle);
            this.pnlSearchSection.Controls.Add(this.lblStartTime);
            this.pnlSearchSection.Controls.Add(this.lblEndTime);
            this.pnlSearchSection.Controls.Add(this.dtpStartTime);
            this.pnlSearchSection.Controls.Add(this.dtpEndTime);
            this.pnlSearchSection.Location = new System.Drawing.Point(24, 80);
            this.pnlSearchSection.Name = "pnlSearchSection";
            this.pnlSearchSection.Size = new System.Drawing.Size(418, 140);
            this.pnlSearchSection.TabIndex = 1;
            // 
            // lblSearchSectionTitle
            // 
            this.lblSearchSectionTitle.AutoSize = true;
            this.lblSearchSectionTitle.Font = new System.Drawing.Font("맑은 고딕", 9F, System.Drawing.FontStyle.Bold, System.Drawing.GraphicsUnit.Point, ((byte)(129)));
            this.lblSearchSectionTitle.ForeColor = System.Drawing.Color.FromArgb(((int)(((byte)(112)))), ((int)(((byte)(124)))), ((int)(((byte)(146)))));
            this.lblSearchSectionTitle.Location = new System.Drawing.Point(18, 18);
            this.lblSearchSectionTitle.Name = "lblSearchSectionTitle";
            this.lblSearchSectionTitle.Size = new System.Drawing.Size(59, 15);
            this.lblSearchSectionTitle.TabIndex = 0;
            this.lblSearchSectionTitle.Text = "검색 기간";
            // 
            // lblStartTime
            // 
            this.lblStartTime.AutoSize = true;
            this.lblStartTime.Font = new System.Drawing.Font("Segoe UI", 9.5F);
            this.lblStartTime.Location = new System.Drawing.Point(18, 57);
            this.lblStartTime.Name = "lblStartTime";
            this.lblStartTime.Size = new System.Drawing.Size(67, 17);
            this.lblStartTime.TabIndex = 1;
            this.lblStartTime.Text = "Start Time";
            // 
            // lblEndTime
            // 
            this.lblEndTime.AutoSize = true;
            this.lblEndTime.Font = new System.Drawing.Font("Segoe UI", 9.5F);
            this.lblEndTime.Location = new System.Drawing.Point(18, 97);
            this.lblEndTime.Name = "lblEndTime";
            this.lblEndTime.Size = new System.Drawing.Size(62, 17);
            this.lblEndTime.TabIndex = 2;
            this.lblEndTime.Text = "End Time";
            // 
            // dtpStartTime
            // 
            this.dtpStartTime.CalendarFont = new System.Drawing.Font("Segoe UI", 9F);
            this.dtpStartTime.CustomFormat = "yyyy-MM-dd HH:mm:ss";
            this.dtpStartTime.Font = new System.Drawing.Font("Segoe UI", 9.5F);
            this.dtpStartTime.Format = System.Windows.Forms.DateTimePickerFormat.Custom;
            this.dtpStartTime.Location = new System.Drawing.Point(118, 51);
            this.dtpStartTime.Name = "dtpStartTime";
            this.dtpStartTime.Size = new System.Drawing.Size(270, 24);
            this.dtpStartTime.TabIndex = 3;
            // 
            // dtpEndTime
            // 
            this.dtpEndTime.CalendarFont = new System.Drawing.Font("Segoe UI", 9F);
            this.dtpEndTime.CustomFormat = "yyyy-MM-dd HH:mm:ss";
            this.dtpEndTime.Font = new System.Drawing.Font("Segoe UI", 9.5F);
            this.dtpEndTime.Format = System.Windows.Forms.DateTimePickerFormat.Custom;
            this.dtpEndTime.Location = new System.Drawing.Point(118, 91);
            this.dtpEndTime.Name = "dtpEndTime";
            this.dtpEndTime.Size = new System.Drawing.Size(270, 24);
            this.dtpEndTime.TabIndex = 4;
            // 
            // pnlConditionSection
            // 
            this.pnlConditionSection.BackColor = System.Drawing.Color.White;
            this.pnlConditionSection.BorderStyle = System.Windows.Forms.BorderStyle.FixedSingle;
            this.pnlConditionSection.Controls.Add(this.lblConditionSectionTitle);
            this.pnlConditionSection.Controls.Add(this.lblRecipeName);
            this.pnlConditionSection.Controls.Add(this.txtRecipeName);
            this.pnlConditionSection.Controls.Add(this.lblStep);
            this.pnlConditionSection.Controls.Add(this.cboStep);
            this.pnlConditionSection.Controls.Add(this.lblPower);
            this.pnlConditionSection.Controls.Add(this.txtMinPower);
            this.pnlConditionSection.Controls.Add(this.lblPowerTilde);
            this.pnlConditionSection.Controls.Add(this.txtMaxPower);
            this.pnlConditionSection.Location = new System.Drawing.Point(24, 236);
            this.pnlConditionSection.Name = "pnlConditionSection";
            this.pnlConditionSection.Size = new System.Drawing.Size(418, 190);
            this.pnlConditionSection.TabIndex = 2;
            // 
            // lblConditionSectionTitle
            // 
            this.lblConditionSectionTitle.AutoSize = true;
            this.lblConditionSectionTitle.Font = new System.Drawing.Font("맑은 고딕", 9F, System.Drawing.FontStyle.Bold, System.Drawing.GraphicsUnit.Point, ((byte)(129)));
            this.lblConditionSectionTitle.ForeColor = System.Drawing.Color.FromArgb(((int)(((byte)(112)))), ((int)(((byte)(124)))), ((int)(((byte)(146)))));
            this.lblConditionSectionTitle.Location = new System.Drawing.Point(18, 18);
            this.lblConditionSectionTitle.Name = "lblConditionSectionTitle";
            this.lblConditionSectionTitle.Size = new System.Drawing.Size(59, 15);
            this.lblConditionSectionTitle.TabIndex = 0;
            this.lblConditionSectionTitle.Text = "검색 조건";
            // 
            // lblRecipeName
            // 
            this.lblRecipeName.AutoSize = true;
            this.lblRecipeName.Font = new System.Drawing.Font("Segoe UI", 9.5F);
            this.lblRecipeName.Location = new System.Drawing.Point(18, 58);
            this.lblRecipeName.Name = "lblRecipeName";
            this.lblRecipeName.Size = new System.Drawing.Size(86, 17);
            this.lblRecipeName.TabIndex = 1;
            this.lblRecipeName.Text = "Recipe Name";
            // 
            // txtRecipeName
            // 
            this.txtRecipeName.BorderStyle = System.Windows.Forms.BorderStyle.FixedSingle;
            this.txtRecipeName.Font = new System.Drawing.Font("Segoe UI", 9.5F);
            this.txtRecipeName.Location = new System.Drawing.Point(118, 54);
            this.txtRecipeName.Name = "txtRecipeName";
            this.txtRecipeName.Size = new System.Drawing.Size(270, 24);
            this.txtRecipeName.TabIndex = 2;
            // 
            // lblStep
            // 
            this.lblStep.AutoSize = true;
            this.lblStep.Font = new System.Drawing.Font("Segoe UI", 9.5F);
            this.lblStep.Location = new System.Drawing.Point(18, 98);
            this.lblStep.Name = "lblStep";
            this.lblStep.Size = new System.Drawing.Size(34, 17);
            this.lblStep.TabIndex = 3;
            this.lblStep.Text = "Step";
            // 
            // cboStep
            // 
            this.cboStep.DropDownStyle = System.Windows.Forms.ComboBoxStyle.DropDownList;
            this.cboStep.Font = new System.Drawing.Font("Segoe UI", 9.5F);
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
            "8"});
            this.cboStep.Location = new System.Drawing.Point(118, 94);
            this.cboStep.Name = "cboStep";
            this.cboStep.Size = new System.Drawing.Size(270, 25);
            this.cboStep.TabIndex = 4;
            // 
            // lblPower
            // 
            this.lblPower.AutoSize = true;
            this.lblPower.Font = new System.Drawing.Font("Segoe UI", 9.5F);
            this.lblPower.Location = new System.Drawing.Point(18, 138);
            this.lblPower.Name = "lblPower";
            this.lblPower.Size = new System.Drawing.Size(68, 17);
            this.lblPower.TabIndex = 5;
            this.lblPower.Text = "Power (W)";
            // 
            // txtMinPower
            // 
            this.txtMinPower.BorderStyle = System.Windows.Forms.BorderStyle.FixedSingle;
            this.txtMinPower.Font = new System.Drawing.Font("Segoe UI", 9.5F);
            this.txtMinPower.Location = new System.Drawing.Point(118, 134);
            this.txtMinPower.Name = "txtMinPower";
            this.txtMinPower.Size = new System.Drawing.Size(115, 24);
            this.txtMinPower.TabIndex = 6;
            // 
            // lblPowerTilde
            // 
            this.lblPowerTilde.AutoSize = true;
            this.lblPowerTilde.Font = new System.Drawing.Font("Segoe UI", 10F);
            this.lblPowerTilde.Location = new System.Drawing.Point(244, 137);
            this.lblPowerTilde.Name = "lblPowerTilde";
            this.lblPowerTilde.Size = new System.Drawing.Size(19, 19);
            this.lblPowerTilde.TabIndex = 7;
            this.lblPowerTilde.Text = "~";
            // 
            // txtMaxPower
            // 
            this.txtMaxPower.BorderStyle = System.Windows.Forms.BorderStyle.FixedSingle;
            this.txtMaxPower.Font = new System.Drawing.Font("Segoe UI", 9.5F);
            this.txtMaxPower.Location = new System.Drawing.Point(273, 134);
            this.txtMaxPower.Name = "txtMaxPower";
            this.txtMaxPower.Size = new System.Drawing.Size(115, 24);
            this.txtMaxPower.TabIndex = 8;
            // 
            // btnSave
            // 
            this.btnSave.BackColor = System.Drawing.Color.White;
            this.btnSave.Cursor = System.Windows.Forms.Cursors.Hand;
            this.btnSave.FlatStyle = System.Windows.Forms.FlatStyle.Flat;
            this.btnSave.Font = new System.Drawing.Font("맑은 고딕", 10F, System.Drawing.FontStyle.Bold, System.Drawing.GraphicsUnit.Point, ((byte)(129)));
            this.btnSave.ForeColor = System.Drawing.Color.Black;
            this.btnSave.Location = new System.Drawing.Point(24, 448);
            this.btnSave.Name = "btnSave";
            this.btnSave.Size = new System.Drawing.Size(188, 44);
            this.btnSave.TabIndex = 3;
            this.btnSave.Text = "저장";
            this.btnSave.UseVisualStyleBackColor = false;
            this.btnSave.Click += new System.EventHandler(this.btnSave_Click);
            // 
            // btnSearch
            // 
            this.btnSearch.BackColor = System.Drawing.Color.FromArgb(((int)(((byte)(71)))), ((int)(((byte)(99)))), ((int)(((byte)(236)))));
            this.btnSearch.Cursor = System.Windows.Forms.Cursors.Hand;
            this.btnSearch.FlatStyle = System.Windows.Forms.FlatStyle.Flat;
            this.btnSearch.Font = new System.Drawing.Font("맑은 고딕", 10F, System.Drawing.FontStyle.Bold, System.Drawing.GraphicsUnit.Point, ((byte)(129)));
            this.btnSearch.ForeColor = System.Drawing.Color.White;
            this.btnSearch.Location = new System.Drawing.Point(224, 448);
            this.btnSearch.Name = "btnSearch";
            this.btnSearch.Size = new System.Drawing.Size(218, 44);
            this.btnSearch.TabIndex = 4;
            this.btnSearch.Text = "검색";
            this.btnSearch.UseVisualStyleBackColor = false;
            this.btnSearch.Click += new System.EventHandler(this.btnSearch_Click);
            // 
            // ParameterForm
            // 
            this.AutoScaleDimensions = new System.Drawing.SizeF(7F, 12F);
            this.AutoScaleMode = System.Windows.Forms.AutoScaleMode.Font;
            this.BackColor = System.Drawing.Color.White;
            this.CancelButton = this.btnClose;
            this.ClientSize = new System.Drawing.Size(466, 514);
            this.Controls.Add(this.btnSave);
            this.Controls.Add(this.btnSearch);
            this.Controls.Add(this.pnlConditionSection);
            this.Controls.Add(this.pnlSearchSection);
            this.Controls.Add(this.pnlHeader);
            this.FormBorderStyle = System.Windows.Forms.FormBorderStyle.None;
            this.Name = "ParameterForm";
            this.StartPosition = System.Windows.Forms.FormStartPosition.CenterParent;
            this.Text = "Parameter Search";
            this.Load += new System.EventHandler(this.ParameterForm_Load);
            this.pnlHeader.ResumeLayout(false);
            this.pnlHeader.PerformLayout();
            this.pnlSearchSection.ResumeLayout(false);
            this.pnlSearchSection.PerformLayout();
            this.pnlConditionSection.ResumeLayout(false);
            this.pnlConditionSection.PerformLayout();
            this.ResumeLayout(false);

        }

        #endregion

        private System.Windows.Forms.Panel pnlHeader;
        private System.Windows.Forms.Button btnClose;
        private System.Windows.Forms.Label lblTitle;
        private System.Windows.Forms.Panel pnlSearchSection;
        private System.Windows.Forms.Label lblSearchSectionTitle;
        private System.Windows.Forms.Label lblStartTime;
        private System.Windows.Forms.Label lblEndTime;
        private System.Windows.Forms.DateTimePicker dtpStartTime;
        private System.Windows.Forms.DateTimePicker dtpEndTime;
        private System.Windows.Forms.Panel pnlConditionSection;
        private System.Windows.Forms.Label lblConditionSectionTitle;
        private System.Windows.Forms.Label lblRecipeName;
        private System.Windows.Forms.TextBox txtRecipeName;
        private System.Windows.Forms.Label lblStep;
        private System.Windows.Forms.ComboBox cboStep;
        private System.Windows.Forms.Label lblPower;
        private System.Windows.Forms.TextBox txtMinPower;
        private System.Windows.Forms.Label lblPowerTilde;
        private System.Windows.Forms.TextBox txtMaxPower;
        private System.Windows.Forms.Button btnSave;
        private System.Windows.Forms.Button btnSearch;
    }
}