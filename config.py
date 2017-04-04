# -*- coding: utf-8 -*-
import re

# 日志输出格式
# FORMAT = 'PID:%(process)d - %(levelname)s [%(lineno)d]: [%(funcName)s] %(message)s'
FORMAT = 'PID:%(process)d - %(levelname)s: %(message)s'

# 映射表保存位置
links_map_directory = 'links_map'

# 所有正则
# 匹配文档的开头
docRE = re.compile(r'<doc id="(\d+)" url="(.*?)" title="(.*?)">')
# 匹配文本中的标签
tagRE = re.compile(r'<[^>]+>', re.S)
# 提取[[和]]之间的内容，并且内容中不能包含[[
linkRE_1 = re.compile(r'\[\[((?:(?!\]\]).)+)\]\]')
# 提取{{和}}之间的内容，并且内容中不能包含[[
linkRE_2 = re.compile(r'\{\{((?:(?!\}\}).)+)\}\}')
# 提取 token/POS/lemma 中的lemma
ExtractLemmaRE = re.compile(r'[^\s\/]+\/[^\s\/]+\/([^\s\/]+)')
# 提取 token/POS/lemma 中的token
ExtractTokenRE = re.compile(r'([^\s\/]+)\/[^\s\/]+\/[^\s\/]+')
# 文本查找时用来构建查找特定词的正则
re_word_base = r'[^\s\/]+\/[^\s\/]+\/{}'

# 文本中存在如下字符串，报错
ErrorToken = ['{{', '}}']