

# 形式语言与自动机上机作业

实现了上下文无关文法转Greibach，Greibach范式生成PDA部分仅在报告中提供设计思路。

 
## 代码运行
 - 直接运行main.py文件即可。
 - 程序从txt文本文件中读取文法，文法约定为如下形式：
    ```
    ??>?
    ??>?|?
    ??>?,?|?,?,?
    ```
    其中?>用于分割产生式左侧的非终结符和右侧的符号，产生式右侧的符号用“，”分割，“|”用于分割不同产生式。约定?为空，所有非终结符均以大写字母开头，所有终结符均以小写字母开头。
 - 项目中提供了一些文法的例子，替换输入文法在main.py文件中更改路径即可更换，如有需要也可按照上述格式自行设计文法。