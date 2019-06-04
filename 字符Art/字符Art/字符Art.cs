



#region Using
// Using
// 自带
using System;
using System.Collections.Generic;
//
// 添加
using System.Drawing;
using System.Drawing.Drawing2D;
using System.IO;
using System.Text;
#endregion

// Color.ToArgb()值结构：
// 字节方向：高 → 低
// 序号：		1		2								3		4			5		6				7		8
// 代表意义：透明值（Α|α，Alpha）		红（Red）		绿（Green）		蓝（Blue）

// 候选颜色空间：
// 底数		指数		幂										位数				名
// 2			8			256									3					灰度|黑白
// 2			9			512									3					
// 2			12		4096								4					
// 2			15		3 2768								5					
// 2			16		6 5536								5					6 5536色
// 2			18		26 2144							6					26万色
// 2			21		209 7152							7					
// 2			24		1677 7216						8					24位真·彩色|RGB|1600万色|1677 7216色
// 2			27		1 3421 7728					9					
// 2			30		10 7374 1824					10				10位深·彩色
// 2			32		42 9496 7296					10				ARGB（透明|α通道+RGB）
// 2			33		85 8993 4592					10				
// 2			36		687 1947 6736				11				12位深·彩色
// 2			39		5497 5581 3888				12				
// 2			42		4 3980 4651 1104			13				
// 2			45		35 1843 7208 8832			14				
// 2			48		281 4749 7671 0656		15				16位深·彩色

namespace 字符Art
{
	public class 泛ASCIIArt
	{
		#region 构造器
		// 构造器
		public 泛ASCIIArt(Int32 缩放因数_输入 = 1) => 缩放因数 = 缩放因数_输入;
		#endregion

		#region 字段
		// 字段
		#region 常量
		// 常量|只读
		// 等宽字体中，不同字体处理不同字符分集的范围不同，且不同的分集宽度不同，最佳实践是泛ASCII字符集 + MS Gothic字体（来源：https://qiita.com/good_kobe/items/7c19a0bc589fb44ee07b）
		// 全角|部分非ASCII效果不好，横向太宽
		// 含符号容易出现识别为特殊含义，影响结果效果
		public const String 字符集 =
			" "		// 作为背景的填充
			+ "0123456789"
			+ "ABCDEFGHIJKLMNOPQRSTUVWXYZ"
			+ "abcdefghijklmnopqrstuvwxyz"
			+ "ÄÖÜßäöü"
			+ "ｦｧｨｩｪｫｬｭｮｯｱｲｳｴｵｶｷｸｹｺｻｼｽｾｿﾀﾁﾂﾃﾄﾅﾆﾇﾈﾉﾊﾋﾌﾍﾎﾏﾐﾑﾒﾓﾔﾕﾖﾗﾘﾙﾚﾛﾜﾝ"
			// 预留
			+ ""
			+ ""
			+ ""
			+ ""
			+ ""
			+ ""
			+ ""
			+ "";		// 数字 + 多国字母，即纯文字
		private const Int32 位进制数 = 8;
		private const Int32 颜色次序模 = 4;		// 满足一索引值的减法以下映射：
																	// 1 → 3
																	// 2 → 2
																	// 3 → 1
		private const Int32 红色次序 = 1;
		private const Int32 绿色次序 = 2;
		private const Int32 蓝色次序 = 3;
		private readonly Point 原点 = default;		// 代表new Point(0, 0)，即赋值为点(0, 0)
																		// 这是1个标准点位，充当某种“default”
																		// 计算机的像素坐标体系与数学中的不同，虽实际操作仍是〇始，但不同于数学中视为原点（(0, 0)）用，而是对应其(1, 1)的ZeroIndexed()，故不可混淆
		public const Int32 字符图边长 = 500;		// 正方形的字体背景较适于观察
		public const Int32 字号 = 300;		// Pound
		private const Int32 灰度钝化块大小 = 2;
		#endregion
		#region 变量
		// 变量
		// 构造器赋值
		String 字体名 = @$"MS Gothic";
		private Int32 缩放因数 = default;
		#endregion
		#endregion

		#region 属性
		// 属性
		private Int32 红色移位掩码 => 位进制数 * 转换颜色次序(红色次序);
		private Int32 绿色移位掩码 => 位进制数 * 转换颜色次序(绿色次序);
		private Int32 蓝色移位掩码 => 位进制数 * 转换颜色次序(蓝色次序);
		private Int32 红色掩码 => Byte.MaxValue << 红色移位掩码;
		private Int32 绿色掩码 => Byte.MaxValue << 绿色移位掩码;
		private Int32 蓝色掩码 => Byte.MaxValue << 蓝色移位掩码;
		private Int32 复颜色掩码 => 红色掩码 | 绿色掩码 | 蓝色掩码;
		private Int32 像素深度 => OneIndexed(Byte.MaxValue);		// 二者完美契合，但前者赋予了更具体的意义
		#endregion

		#region 方法
		// 方法
		public StringBuilder 生成(Image 源图_输入, Char[] 填充源组_输入)
		{
			// ！源合法性检测

			// 自适应修正的文件大小，防止打开时卡顿
			Decimal 比例 = Convert.ToDecimal(源图_输入.Width) / 源图_输入.Height;
			StringBuilder 目标内容_输出 = new StringBuilder();
			Int32 目标索引 = default;
			Boolean toggle = default;
			Point 坐标索引 = 原点;
			Image 参考源 = default;
			Point 起点 = default;		// 强调不需要是原点
			Color 源色 = default;
			Bitmap 源图 = new Bitmap(源图_输入);

			// 调整显示比例的方式
			// 1.设置比例：使用屏幕|指定长宽缩放索引上限；直接乘
			// 2.设置增幅：索引步进增大，主要是横坐标，如：宽缩进量 : 高缩进量 = 1 : 2
			// ？3.设置toggle
			// ？4.增大行间距（增加空白行）：可行，但淡化了画面

			// 增幅设为4倍为了兼容4K分辨率的图片能正常显示出来
			// ？此处使用先列遍历是因为方便横坐标修改增幅
			// ！以较小边为行更适合，多数编辑器的行有限制
			for( ; 坐标索引.Y <= ZeroIndexed(源图_输入.Height); 坐标索引.Y += 缩放因数)		// 行锁定
			{
				for(坐标索引.X = default; 坐标索引.X <= ZeroIndexed(源图_输入.Width); 坐标索引.X += 缩放因数)		// 列锁定
				{
					起点 = 坐标索引;

					// 对应序位算法，单色
					//源色 = 源图.GetPixel(起点.X, 起点.Y);		// 对应步进应为1才能保障来源是准确的
					// 对应序位算法，平均
					参考源 = 获取图片区域(源图, 起点);		// ！Rectangle的构造不优雅，需要引入Point、Size类型

					if(!toggle)
					{
						// 对应序位算法，单色
						//目标索引 = ZeroIndexed(Convert.ToInt32(Math.Round(获取平均亮度(源色) / 像素深度 * 填充源组_输入.Length)));		// 使用Math.Round()防止后期使用时的转换直接向下取整损失部分精确度
																																																		// 该算法既可用于256字符以下的输入字符集，又可用于以上的
																																																		// ！获取在颜色空间占比（？）的逻辑考虑提取函数
																																																		// ！纯黑色会引发问题，因UInt64的〇向前()即UInt64.MaxValue
																																																		// ！需要补齐对应的256灰度空间时的处理
																																																		// ！考虑和图片填充版的核心函数合并逻辑
						// 对应序位算法，平均
						目标索引 = ZeroIndexed(Convert.ToInt32(Math.Round(获取平均亮度(参考源) / 像素深度 * 填充源组_输入.Length)));

						目标内容_输出.Append(填充源组_输入[目标索引]);
					}
					else
					{
						// 占位
					}
				}

				if(!toggle)		// 老外的智慧：尽量减少参差|变形，来源：https://dotnetfiddle.net/neyqDF
				{
					目标内容_输出.Append(Environment.NewLine);

					toggle = true;
				}
				else
				{
					toggle = false;
				}
			}

			// 终处理
			源图_输入.Dispose();

			return 目标内容_输出;
		}

		// 本来输入、输出的类型应该是对应的，但是字符的调用方直接应用Char[]，故二者不对等，也跟String与Char[]有关有关
		public Char[] 生成填充源(String 填充源_输入)
		{
			Int32 长度 = 填充源_输入.Length;
			Image 容器 = default;
			Decimal 亮度容器 = default;
			Char[] 填充字符组 = 填充源_输入.ToCharArray();
			List<(Decimal 亮度, Char 字符)> 排序组 = new List<(Decimal 亮度, Char 字符)>();
			StringBuilder 填充字符组_输出 = new StringBuilder();

			for(Int32 索引 = default; 索引 <= ZeroIndexed(填充字符组.Length); 索引++)
			{
				容器 = 绘制图片(填充字符组[索引].ToString());

				//亮度值组[索引] = Convert.ToInt32(获取平均亮度(容器));
				亮度容器 = 获取平均亮度(容器);
				排序组.Add((亮度容器, 填充字符组[索引]));

				// 终处理
				容器.Dispose();
			}

			// 排序
			// 按Unicode码顺序的字符组作Item。Decimal[]作Key会导致排序Key；而Int32[]则不能正常排序
			排序组.Sort((前, 后) => (前.亮度 <= 后.亮度) ? -1 : 1);		// Comparison返回值含义：
																								// -1：小于
																								// 0：相等
																								// 1：大于

			foreach((_, Char 字符) in 排序组)
			{
				填充字符组_输出.Append(字符);
			}

			return 填充字符组_输出.ToString().ToCharArray();
		}

		// 理论上只用于各分量，以匿名|值元组类型是便于分量的次序化标识
		private (Int32 红, Int32 绿, Int32 蓝) 统计颜色(Image 源图_输入)
		{
			(Int32 红, Int32 绿, Int32 蓝) 颜色计数_输出 = default;
			Point 索引 = 原点;
			(Int32 红, Int32 绿, Int32 蓝) 容器 = default;
			Bitmap 源图 = new Bitmap(源图_输入);

			for( ; 索引.Y <= ZeroIndexed(源图_输入.Height); 索引.Y++)
			{
				for(索引.X = default; 索引.X <= ZeroIndexed(源图_输入.Width); 索引.X++)
				{
					容器 = 获取颜色分量(源图.GetPixel(索引.X, 索引.Y));		// ？没有Point版本

					颜色计数_输出 = Add(颜色计数_输出, 容器);
				}
			}

			// 终处理
			//源图_输入.Dispose();		// ？可行

			return 颜色计数_输出;
		}

		private (Int32 红, Int32 绿, Int32 蓝) 获取颜色分量(Color 颜色_输入)
		{
			(Int32 红, Int32 绿, Int32 蓝) 颜色 = default;
			Int32 色 = 颜色_输入.ToArgb() & 复颜色掩码;

			// ！此部分处理需要提取函数
			颜色.红 = OneIndexed((色 & 红色掩码) >> (红色移位掩码));
			颜色.绿 = OneIndexed((色 & 绿色掩码) >> (绿色移位掩码));
			颜色.蓝 = OneIndexed((色 & 蓝色掩码) >> (蓝色移位掩码));

			return 颜色;
		}

		private Decimal 获取平均亮度(Image 源图_输入) => 获取平均亮度(获取平均颜色(源图_输入));

		// 也是亮度（Luminance），也是灰度（Gray）
		// 这是1-Indexed的各颜色分量进行的运算，公式也是1-Indexed的
		// 亦可称为：生成标识()
		private Decimal 获取平均亮度((Int32 红, Int32 绿, Int32 蓝) 源色_输入)
		{
			// 简易算法：3原色值取算术平均
			//return (OneIndexed(源色_输入.R) + OneIndexed(源色_输入.G) + OneIndexed(源色_输入.B)) / 原色数);

			// 经典算法：NTSC（National Television Standards Committee）电视制式的色彩空间YIQ中的Y（Luminance）
			// 来源：https://stackoverflow.com/questions/596216/formula-to-determine-brightness-of-rgb-color
			return 0.2126M * 源色_输入.红 + 0.7152M * 源色_输入.绿 + 0.0722M * 源色_输入.蓝;		// 标准版，对应某种颜色空间
																																					// 1063 : 3576 : 361，3者和为5000
			//return 0.299M * 源色_输入.红 + 0.587M * 源色_输入.绿 + 0.114M * 源色_输入.蓝;		// 适用人感知的版本
			//return Math.Pow(0.299M * Math.Pow(源色_输入.红, 2) + 0.587 * Math.Pow(源色_输入.绿, 2) + 0.114M * Math.Pow(源色_输入.蓝, 2), 0.5M);		// √(0.299 * R^2 + 0.587 * G^2 + 0.114 * B^2)
																																																										// 适用人感知的版本，计算上更慢
			//
			// 扩展版
			//return Convert.ToUInt64(Math.Round((0.2126M * 源色_输入.红 + 0.7152M * 源色_输入.绿 + 0.0722M * 源色_输入.绿) * 映射比));		// 将 ∈ [1, 256]的亮度比映射到 ∈ [1, 绘制源数量]上面

			// “遵循自然”的算法
			//return OneIndexed(源色_输入.GetBrightness() * ZeroIndexed(像素深度));		// 首先，这是个比率，不是均值；其次，内部实现非常粗糙
																																// 因其是比率，故算“度值”的话需要先还原，即 × 像素深度
																																// ！这是0-Indexed下进行的计算，有设计误差
		}

		private (Int32 红, Int32 绿, Int32 蓝) 获取平均颜色(Image 源图_输入)
		{
			Int64 像素空间 = 源图_输入.Width * 源图_输入.Height;
			(Int32 红, Int32 绿, Int32 蓝) 颜色_输出 = default;

			// 平均化
			// 求整图的RGB通道平均颜色，算术平均，可换为更高级平均算法
			颜色_输出 = Divide(统计颜色(源图_输入), 像素空间);

			//return OneIndexed(容器.ToArgb() & 复颜色掩码);
			//
			//容器 = Color.FromArgb(Convert.ToInt32(ZeroIndexed(Convert.ToUInt64(Math.Round(红色计数 * 1M / 像素空间)))), Convert.ToInt32(ZeroIndexed(Convert.ToUInt64(Math.Round(绿色计数 * 1M / 像素空间)))), Convert.ToInt32(ZeroIndexed(Convert.ToUInt64(Math.Round(蓝色计数 * 1M / 像素空间)))));
			//return 钝化颜色深度(容器);		// ！不非得有
			//return 容器;

			return 颜色_输出;
		}

		public Image 绘制图片(String 源字符_输入)
		{
			Color 前景色 = Color.Black;
			Color 底色 = Color.White;

			return 绘制图片_核心(源字符_输入, 字体名, 前景色, 底色);
		}

		// 虽然Char更符合，但双方都需要额外转换，故直接用String
		// 来源：？
		// ！其实字形是矢量图，应该可以直接通过ImageFile获取其亮度，且更合适
		private Image 绘制图片_核心(String 源字符_输入, String 字体名_输入, Color 前景色_输入, Color 底色_输入)		// ！传递Bitmap对象实体还是文件路径待考虑
		{
			// 定义
			Graphics 生成器 = default;
			Font 字体 = new Font(字体名_输入, 字号, FontStyle.Regular, GraphicsUnit.Pixel);		// ！待测试
			Point 目标起点 = 原点;
			Size 目标大小 = new Size(字符图边长, 字符图边长);		// 大小不需要0-Indexed值
			Rectangle 目标域 = new Rectangle(目标起点, 目标大小);
			Image 目标图_输出 = new Bitmap(目标域.Width, 目标域.Height);
			SolidBrush 绘制器 = new SolidBrush(前景色_输入);

			// 赋值
			// 设置生成器
			生成器 = Graphics.FromImage(目标图_输出);
			// 背景色
			生成器.Clear(底色_输入);		// 透明背景增大黑色感，白色效果更好
														// 比FillRectangle()|FillRegion()省事
			// 绘制质量
			生成器.CompositingQuality = CompositingQuality.HighQuality;		// 合成质量
			生成器.SmoothingMode = SmoothingMode.HighQuality;		// 平滑模式质量
			生成器.InterpolationMode = InterpolationMode.HighQualityBicubic;		// 插值算法质量

			// 处理
			生成器.DrawString(源字符_输入.ToString(), 字体, 绘制器, 目标域);

			// 终处理
			//源图_输入.Dispose();
			生成器.Dispose();

			return 目标图_输出;
		}

		public Image 获取图片区域(Image 源图_输入, Point 源起点_输入)
		{
			// 官方推荐版
			// 定义+赋值
			//Size 源大小 = new Size(填充边长, 填充边长);		// 大小不需要0-Indexed值
			//Rectangle 源域 = new Rectangle(源起点_输入, 源大小);
			//return 源图_输入.Clone(源域, PixelFormat.Format32bppArgb);

			// Graphics.DrawImage()版
			// 定义+赋值
			Size 源大小 = new Size(缩放因数, 缩放因数);		// 大小不需要0-Indexed值
			Rectangle 源域 = new Rectangle(源起点_输入, 源大小);

			return 获取图片区域(源图_输入, 源域);
		}

		public Image 获取图片区域(Image 源图_输入, Rectangle 源域_输入)
		{
			//Bitmap 目标图_输出 = 源图_输入.Clone(获取域_输入, PixelFormat.Format32bppArgb);		// 官方推荐版

			Point 目标起点 = 原点;
			Size 目标大小 = 源域_输入.Size;		// 大小不需要ZeroIndexed0-Indexed值
																// 将指定大小的区域复制下来
			Rectangle 目标域 = new Rectangle(目标起点, 目标大小);

			return 绘制图片_核心(源图_输入, 源域_输入, 目标域);
		}

		private Image 绘制图片_核心(Image 源图_输入, Rectangle 源域_输入, Rectangle 目标域_输入)
		{
			Image 目标图 = new Bitmap(目标域_输入.Size.Width, 目标域_输入.Size.Height);		// ？没有Size版本的
			Color 底色 = Color.Transparent;

			return 绘制图片_核心(源图_输入, 目标图, 源域_输入, 目标域_输入, 底色);
		}

		private Image 绘制图片_核心(Image 源图_输入, Image 目标图_输入_输出, Rectangle 源域_输入, Rectangle 目标域_输入, Color 底色_输入)		// ！传递Bitmap对象实体还是文件路径待考虑
		{
			// 定义
			Graphics 生成器 = default;

			// 赋值
			// 设置生成器
			if(目标图_输入_输出 == default)
			{
				// 背景色
				目标图_输入_输出 = new Bitmap(目标域_输入.Size.Width, 目标域_输入.Size.Height);
				生成器 = Graphics.FromImage(目标图_输入_输出);
				生成器.Clear(底色_输入);		// 透明背景增大黑色感，白色效果更好
														// 比FillRectangle()|FillRegion()省事
			}
			else
			{
				生成器 = Graphics.FromImage(目标图_输入_输出);
			}
			// 绘制质量
			生成器.CompositingQuality = CompositingQuality.HighQuality;		// 合成质量
			生成器.SmoothingMode = SmoothingMode.HighQuality;		// 平滑模式质量
			生成器.InterpolationMode = InterpolationMode.HighQualityBicubic;		// 插值算法质量

			// 处理
			生成器.DrawImage(源图_输入, 目标域_输入, 源域_输入, GraphicsUnit.Pixel);		// ！默认的填充方式是拉伸至正方形，除了比例乱了没啥大事

			// 终处理
			//源图_输入.Dispose();
			生成器.Dispose();

			return 目标图_输入_输出;
		}

		// 一般+的算法
		// 灰度高占比的单项 → 多灰度阶层，即纵向改横向，即提高对比度，尽量更多突出各部分
		// 主要面向色彩集中的图，可选
		// 来源：？https://github.com/defineYIDA/picequalization
		public Image 直方图均衡化(Image 源图_输入)		// ！待重构
																				// ！3原色颜色分度的处理代码需要提取函数
		{
			Int64 像素空间 = 源图_输入.Width * 源图_输入.Height;
			(Int32[] 红, Int32[] 绿, Int32[] 蓝) 亮度组 = (new Int32[像素深度], new Int32[像素深度], new Int32[像素深度]);
			(Decimal[] 红, Decimal[] 绿, Decimal[] 蓝) 亮度密度组 = (new Decimal[像素深度], new Decimal[像素深度], new Decimal[像素深度]);
			Bitmap 目标图_输出 = new Bitmap(源图_输入.Width, 源图_输入.Height);
			(Decimal 红, Decimal 绿, Decimal 蓝) 容器 = default;
			Color 像素 = default;
			Point 坐标索引 = 原点;
			Bitmap 源图 = new Bitmap(源图_输入);

			// 〇始部分
			for( ; 坐标索引.Y <= ZeroIndexed(源图_输入.Height); 坐标索引.Y++)
			{
				for(坐标索引.X = default; 坐标索引.X <= ZeroIndexed(源图_输入.Width); 坐标索引.X++)
				{
					像素 = 源图.GetPixel(坐标索引.X, 坐标索引.Y);

					// 计算各颜色分度值的数量集
					亮度组.红[像素.R]++;
					亮度组.绿[像素.G]++;
					亮度组.蓝[像素.B]++;
				}
			}

			// 计算各颜色值的占比
			for(Int32 索引 = default; 索引 <= ZeroIndexed(像素深度); 索引++)
			{
				亮度密度组.红[索引] = Decimal.Divide(亮度组.红[索引], 像素空间);
				亮度密度组.绿[索引] = Decimal.Divide(亮度组.绿[索引], 像素空间);
				亮度密度组.蓝[索引] = Decimal.Divide(亮度组.蓝[索引], 像素空间);
			}

			// 计算累积百分比
			// ？哪个著名的变换来着
			// ！不是一始，而是防止计算时下限越界，利用这种方法，化简了起始索引的计算：亮度密度组.XXX[default] += 0
			for(Int32 索引 = Next(default); 索引 <= ZeroIndexed(像素深度); 索引++)
			{
				// 向前取，0-Indexed下1始，防止超过上限
				亮度密度组.红[索引] += 亮度密度组.红[Previous(索引)];
				亮度密度组.绿[索引] += 亮度密度组.绿[Previous(索引)];
				亮度密度组.蓝[索引] += 亮度密度组.蓝[Previous(索引)];
			}

			for(坐标索引.Y = default; 坐标索引.Y <= ZeroIndexed(源图_输入.Height); 坐标索引.Y++)
			{
				for(坐标索引.X = default; 坐标索引.X <= ZeroIndexed(源图_输入.Width); 坐标索引.X++)
				{
					像素 = 源图.GetPixel(坐标索引.X, 坐标索引.Y);		// ！没有Point版本

					容器.红 = 像素.R;
					容器.绿 = 像素.G;
					容器.蓝 = 像素.B;

					if(容器.红 == default)
					{
						//容器.红 = default;		// 保持〇亮度映射得也是〇
					}
					else
					{
						// 容器.红 = 源亮度 × 累计百分比
						容器.红 = 亮度密度组.红[Convert.ToInt32(Math.Round(容器.红))] * 像素深度;
					}

					if(容器.绿 == default)
					{
						//容器.绿 = default;		// 保持〇亮度映射得也是〇
					}
					else
					{
						// 容器.绿 = 源亮度 × 累计百分比
						容器.绿 = 亮度密度组.绿[Convert.ToInt32(Math.Round(容器.绿))] * 像素深度;
					}

					if(容器.蓝 == default)
					{
						//容器.蓝 = default;		// 保持〇亮度映射得也是〇
					}
					else
					{
						// 容器.蓝 = 源亮度 × 累计百分比
						容器.蓝 = 亮度密度组.蓝[Convert.ToInt32(Math.Round(容器.蓝))] * 像素深度;
					}

					像素 = Color.FromArgb(ZeroIndexed(Convert.ToInt32(容器.红)), ZeroIndexed(Convert.ToInt32(容器.绿)), ZeroIndexed(Convert.ToInt32(容器.蓝)));		// 此处可切换为执行灰度化

					目标图_输出.SetPixel(坐标索引.X, 坐标索引.Y, 像素);		// 简化了对红色分度值、绿色分度值、蓝色分度值 = default的颜色的处理
																									// ！使用BitmapData的性能更好
																									// ！没有Point版本

					// 终处理
					容器 = default;		// 1代3，nice！
				}
			}

			// 终处理
			源图_输入.Dispose();

			return 目标图_输出;
		}
		#region 工具
		// 工具
		private Int32 OneIndexed(Int32 ZeroIndexed_输入) => Next(ZeroIndexed_输入);
		private Int32 ZeroIndexed(Int32 OneIndexed_输入) => Previous(OneIndexed_输入);
		//
		private Int32 Previous(Int32 源数_输入) => Convert.ToInt32(Previous(Convert.ToUInt64(源数_输入)));
		private UInt64 Previous(UInt64 源数_输入)
		{
			if(源数_输入 != default)
			{
				return 源数_输入 - 1;
			}
			else		// 主要用于统计后颜色值的索引转换处
			{
				return default;
			}
		}
		private Int32 Next(Int32 源数_输入) => 源数_输入 + 1;
		//
		public void 写入文件(StringBuilder 内容_输入, String 路径_输入)		// ？考虑以Object代替，兼容不同类型，但图片似乎不能这么存，则余下的都是文本|类文本的，好像又没必要改Object了
																										// ？Object能否正常识别，仅靠文件格式
		{
			// ！未做合法性检测

			StreamWriter 写入器 = new StreamWriter(new FileStream(路径_输入, FileMode.Create), Encoding.UTF8);		// ！ASCII节约地方；UTF-8通用；UTF-32直接

			写入器.Write(内容_输入);

			// ？不需要写入Flush()

			写入器.Close();

			写入器.Dispose();
		}
		//
		private Int32 转换颜色次序(Int32 源次序_输入) => ZeroIndexed(颜色次序模 - 源次序_输入);
		//
		private Int32 RoundDivide(Int32 被除数_输入, Int64 除数_输入) => Convert.ToInt32(Math.Round(Decimal.Divide(被除数_输入, 除数_输入)));
		private (Int32 红, Int32 绿, Int32 蓝) Add((Int32 红, Int32 绿, Int32 蓝) 被加数_输入, (Int32 红, Int32 绿, Int32 蓝) 加数_输入) => (被加数_输入.红 + 加数_输入.红, 被加数_输入.绿 + 加数_输入.绿, 被加数_输入.蓝 + 加数_输入.蓝);
		private (Int32 红, Int32 绿, Int32 蓝) Divide((Int32 红, Int32 绿, Int32 蓝) 被除数_输入, Int64 除数_输入)
		{
			(Int32 红, Int32 绿, Int32 蓝) 商_输出 = default;

			商_输出.红 = RoundDivide(被除数_输入.红, 除数_输入);
			商_输出.绿 = RoundDivide(被除数_输入.绿, 除数_输入);
			商_输出.蓝 = RoundDivide(被除数_输入.蓝, 除数_输入);

			return 商_输出;
		}
		#endregion
		#endregion
	}
}