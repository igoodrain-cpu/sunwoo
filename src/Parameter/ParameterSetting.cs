using System;
using System.Collections.Generic;
using System.Globalization;
using System.IO;
using System.Text;
using System.Web.Script.Serialization;

namespace Iruza.src.Parameter
{
    internal sealed class ParameterSetting
    {
        public DateTime? StartTime { get; set; }
        public DateTime? EndTime { get; set; }

        public string RecipeName { get; set; }
        public short? StepNum { get; set; }
        public decimal? MinPower { get; set; }
        public decimal? MaxPower { get; set; }

        public static ParameterSetting Load(string filePath)
        {
            if (!File.Exists(filePath))
                throw new FileNotFoundException("ParameterSetting.json 파일을 찾을 수 없습니다.", filePath);

            var json = File.ReadAllText(filePath);
            var serializer = new JavaScriptSerializer();
            var values = serializer.Deserialize<Dictionary<string, object>>(json)
                         ?? new Dictionary<string, object>();

            return new ParameterSetting
            {
                StartTime = ParseDateTime(GetValue(values,
                    "StartTime", "startTime", "StartDateTime", "startDateTime", "시작시간", "시작일시")),
                EndTime = ParseDateTime(GetValue(values,
                    "EndTime", "endTime", "EndDateTime", "endDateTime", "끝시간", "종료시간", "종료일시")),
                RecipeName = GetValue(values,
                    "RecipeName", "recipeName", "레시피명"),
                StepNum = ParseShort(GetValue(values,
                    "StepNum", "stepNum", "Step", "step")),
                MinPower = ParseDecimal(GetValue(values,
                    "MinPower", "minPower")),
                MaxPower = ParseDecimal(GetValue(values,
                    "MaxPower", "maxPower"))
            };
        }

        public static ParameterSetting LoadPara(string filePath)
        {
            if (!File.Exists(filePath))
                throw new FileNotFoundException("ParameterSetting.json 파일을 찾을 수 없습니다.", filePath);

            var json = File.ReadAllText(filePath);
            var serializer = new JavaScriptSerializer();
            var values = serializer.Deserialize<Dictionary<string, object>>(json)
                         ?? new Dictionary<string, object>();

            return new ParameterSetting
            {
                StartTime = ParseDateTime(GetValue(values,
                    "StartTime", "startTime", "StartDateTime", "startDateTime", "시작시간", "시작일시")),
                EndTime = ParseDateTime(GetValue(values,
                    "EndTime", "endTime", "EndDateTime", "endDateTime", "끝시간", "종료시간", "종료일시")),
                RecipeName = GetValue(values,
                    "RecipeName", "recipeName", "레시피명"),
                StepNum = ParseShort(GetValue(values,
                    "StepNum", "stepNum", "Step", "step")),
                MinPower = ParseDecimal(GetValue(values,
                    "MinPower", "minPower")),
                MaxPower = ParseDecimal(GetValue(values,
                    "MaxPower", "maxPower"))
            };
        }

        private static short? ParseShort(string value)
        {
            if (string.IsNullOrWhiteSpace(value))
                return null;

            if (short.TryParse(value, NumberStyles.Integer, CultureInfo.InvariantCulture, out var s))
                return s;

            return null;
        }

        private static decimal? ParseDecimal(string value)
        {
            if (string.IsNullOrWhiteSpace(value))
                return null;

            if (decimal.TryParse(value, NumberStyles.Number, CultureInfo.InvariantCulture, out var d))
                return d;

            return null;
        }


        public void Save(string filePath)
        {
            var serializer = new JavaScriptSerializer();
            var json = serializer.Serialize(new Dictionary<string, string>
            {
                ["StartTime"] = (StartTime ?? DateTime.Now.AddDays(-14)).ToString("yyyy-MM-ddTHH:mm:ss", CultureInfo.InvariantCulture),
                ["EndTime"] = (EndTime ?? DateTime.Now).ToString("yyyy-MM-ddTHH:mm:ss", CultureInfo.InvariantCulture),
                ["RecipeName"] = RecipeName ?? string.Empty,
                ["StepNum"] = StepNum.HasValue ? StepNum.Value.ToString(CultureInfo.InvariantCulture) : string.Empty,
                ["MinPower"] = MinPower.HasValue ? MinPower.Value.ToString(CultureInfo.InvariantCulture) : string.Empty,
                ["MaxPower"] = MaxPower.HasValue ? MaxPower.Value.ToString(CultureInfo.InvariantCulture) : string.Empty
            });

            var directory = Path.GetDirectoryName(filePath);
            if (!string.IsNullOrWhiteSpace(directory) && !Directory.Exists(directory))
                Directory.CreateDirectory(directory);

            File.WriteAllText(filePath, FormatJson(json), Encoding.UTF8);
        }

        private static string GetValue(Dictionary<string, object> values, params string[] keys)
        {
            foreach (var key in keys)
            {
                if (values.TryGetValue(key, out var value) && value != null)
                    return Convert.ToString(value, CultureInfo.InvariantCulture);
            }

            return null;
        }

        private static DateTime? ParseDateTime(string value)
        {
            if (string.IsNullOrWhiteSpace(value))
                return null;

            if (DateTime.TryParse(value, CultureInfo.InvariantCulture, DateTimeStyles.AssumeLocal, out var dt))
                return dt;

            if (DateTime.TryParse(value, CultureInfo.CurrentCulture, DateTimeStyles.AssumeLocal, out dt))
                return dt;

            return null;
        }

        private static string FormatJson(string json)
        {
            return json
                .Replace("{\"", "{\r\n  \"")
                .Replace("\",\"", "\",\r\n  \"")
                .Replace("\"}", "\"\r\n}");
        }
    }
}