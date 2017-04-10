# -*- coding: utf-8 -*-
import os
import sys
import time
import argparse
import fileinput
import random
import re
import pickle
import logging
from multiprocessing import Process, Queue
from multiprocessing import Value

__version__ = '2017040410'

if sys.platform == "win32":
    # On Windows, the best timer is time.clock()
    default_timer = time.clock
else:
    # On most other platforms the best timer is time.time()
    default_timer = time.time


class config(object):
    # 日志输出格式
    # FORMAT = 'PID:%(process)d - %(levelname)s [%(lineno)d]: [%(funcName)s] %(message)s'
    FORMAT = 'PID:%(process)d - %(levelname)s: %(message)s'
    # 将日志保存到文件中,空的话输出到控制台
    log2file = ''
    # 处理多少篇文章后报告速度
    REPORT_NUM = 10

    # 映射表保存位置
    links_map_directory = 'links_map'

    # 所有正则
    # 匹配文档的开头
    docRE = re.compile(r'<doc id="(\d+)" url="(.*?)" title="(.*?)">')
    # 匹配文本中的标签
    tagRE = re.compile(r'<[^>]+>', re.S)
    # 提取[[和]]之间的内容，并且内容中不能包含[[
    linkRE_1 = re.compile(r'\s\[\[((?:(?!\]\]).)+)\]\]\s')
    # 提取[[[和]]]之间的内容，并且内容中不能包含]]]
    linkRE_2 = re.compile(r'\s\[\[\[((?:(?!\]\]\]).)+)\]\]\]\s')
    # 提取 token/POS/lemma 中的lemma
    ExtractLemmaRE = re.compile(r'[^\s\/]*\/[^\s\/]*\/([^\s\/]*)')
    # ExtractLemmaRE = re.compile(r'([^\s\/]*)\/(?:[^\s\/]*\/[^\s\/]*|[^\s\/]*)\/([^\s\/]*)')
    # 提取 token/POS/lemma 中的token
    ExtractTokenRE = re.compile(r'([^\s\/]*)\/[^\s\/]*\/[^\s\/]*')
    # ExtractTokenRE = re.compile(r'([^\s\/]*)\/(?:[^\s\/]*\/[^\s\/]*|[^\s\/]*)\/[^\s\/]*')
    # 文本查找时用来构建查找特定词的正则
    re_word_base = r'[^\s\/]*\/[^\s\/]*\/{}'
    # 多个斜线的问题 .../.../.../...
    re_unnecessary_bias = re.compile(r'([^\s\/]*)\/(?:[^\s\/]*\/([^\s\/]*)|([^\s\/]*))\/([^\s\/]*)')

    # 文本中存在如下字符串，报错
    ErrorToken = ['{{', '}}']


def cpu_count():
    '''
    Returns the number of CPUs in the system
    '''
    if sys.platform == 'win32':
        try:
            num = int(os.environ['NUMBER_OF_PROCESSORS'])
        except (ValueError, KeyError):
            num = 0
    elif 'bsd' in sys.platform or sys.platform == 'darwin':
        comm = '/sbin/sysctl -n hw.ncpu'
        if sys.platform == 'darwin':
            comm = '/usr' + comm
        try:
            with os.popen(comm) as p:
                num = int(p.read())
        except ValueError:
            num = 0
    else:
        try:
            num = os.sysconf('SC_NPROCESSORS_ONLN')
        except (ValueError, OSError, AttributeError):
            num = 0

    if num >= 1:
        return num
    else:
        raise NotImplementedError('cannot determine number of cpus')


class OutputSaver(object):
    def __init__(self, filepath, filename):
        self.filepath = filepath
        self.file = {}
        if filename:
            self.file[filename] = self.open(filename)

    def reserve(self, filename):
        if filename not in self.file:
            self.file[filename] = self.open(filename)

    def write(self, data, filename):
        self.reserve(filename)
        self.file[filename].write(data)

    def close(self):
        if self.file:
            for i in self.file.items():
                i[1].close()

    def open(self, filename):
        return open(self.filepath + '/' + filename, 'w')


def files_from(path):
    for f in os.listdir(path):
        if os.path.isfile('{}/{}'.format(path, f)):
            yield f


def pages_from(input):
    '''
    每次返回一个doc
    :param input:
    :return:
    '''
    id = None
    url = None
    title = None
    in_text = False
    text = []
    for line in input:
        line = line.decode('utf-8').encode('utf-8')
        if in_text:
            if line == '</doc>\n' or line == '</doc>\r\n' or line == '</doc>':
                in_text = False
                all_text = ''.join(text)
                del text
                yield [id, title, url, all_text]
                del all_text
                text = []
            else:
                # 去处html标签
                text.append(line)
        else:
            m = config.docRE.search(line)
            if m:
                title = m.group(3)
                id = m.group(1)
                url = m.group(2)
                in_text = True


def normalize(text):
    '''
    处理文本，去掉一些不规则的字符
    :param text:
    :return:
    '''
    text[0] = text[0].replace('&quot;', '"')
    text[0] = text[0].replace('&#039;', '\'')
    text[0] = text[0].replace('&amp;', '&')

    # .../.../.../...
    def func(m):
        token = m.group(1)
        lemma = m.group(4)
        if m.group(2):
            pos = m.group(2)
        else:
            pos = m.group(3)
        return '{}/{}/{}'.format(token, pos, lemma)

    text[0] = config.re_unnecessary_bias.sub(func, text[0])


def checkNorm(text):
    '''
    检查ErrorToken中在text中出现的字符
    :param text:
    :return:
    '''
    tag = []
    for token in config.ErrorToken:
        if token in text[0]:
            tag.append(token)
    return tag


class DumpRunTime:
    '''
    打印执行时间
    with DumpRunTime('build_link'):
        build_link()
    '''

    def __init__(self, tag):
        self.tag = tag
        self.startTime = default_timer()

    def __enter__(self):
        return self  # 可以返回不同的对象

    def __exit__(self, exc_type, exc_value, exc_tb):
        if exc_tb is None:
            use_time = default_timer() - self.startTime
            logging.debug('[%s] run time is %.4fs', self.tag, use_time)
        else:
            logging.error('[Exit %s]: Exited with %s, %s.', self.tag, str(exc_type), str(exc_value))


def extract_link_block(link_block):
    '''
    [[ word ]] 将会解析成 list([word])
    [[ word1 | word2 ]] 将会解析成 list([word1, word2])，word2是在文中显示的词，word1是将会跳转到的词
    :param link_block:
    :return:
    '''
    link_block = link_block.strip()
    # 过滤Category
    if link_block[0:9] == 'Category:':
        link_list = []
    else:
        # 切分link
        link_list = map(lambda x: x.strip(), link_block.split(' | '))
    return list(link_list)


def AddMap(map, key, value):
    '''
    向映射表中添加相应的key和value
    :param map:
    :param key:
    :param value:
    :return:
    '''
    if key in map:
        if value in map[key]:
            map[key][value] += 1
        else:
            map[key][value] = 1
    else:
        map[key] = {value: 1}


def build_link_map(text, maps):
    '''
    建立映射表
    :param text:
    :param maps:
    :return:
    '''
    link_1 = config.linkRE_1.findall(text[0])
    link_2 = config.linkRE_2.findall(text[0])
    link_1.extend(link_2)
    if link_1:
        for link in map(extract_link_block, link_1):
            # link 中有一个item时，[0]:链接指向本身
            # link 中有两个item时，[0]:指向的目标，[1]:链接的名称
            if len(link) == 1:
                lemma = ' '.join(config.ExtractLemmaRE.findall(link[0]))
                token = ' '.join(config.ExtractTokenRE.findall(link[0]))
                AddMap(maps['Map_lemme2tokens'], lemma, token)
                AddMap(maps['Map_token2wikititles_direct'], token, link[0])
            elif len(link) == 2:
                lemma = ' '.join(config.ExtractLemmaRE.findall(link[0]))
                token = ' '.join(config.ExtractTokenRE.findall(link[0]))
                AddMap(maps['Map_lemme2tokens'], lemma, token)
                AddMap(maps['Map_token2wikititles_direct'], token, link[0])

                lemma = ' '.join(config.ExtractLemmaRE.findall(link[1]))
                token = ' '.join(config.ExtractTokenRE.findall(link[1]))
                AddMap(maps['Map_lemme2tokens'], lemma, token)
                AddMap(maps['Map_token2wikititles_indirect'], token, link[0])
            elif len(link) > 2:
                logging.error("There are multiple '|' in the link, please check. link: %s", str(link))

        # 对Map_lemme2tokens排序，使单词多的排在前面
        maps['Map_lemme2tokens'] = sorted(maps['Map_lemme2tokens'].iteritems(), key=lambda x: x[0].count(' ') + 1,
                                          reverse=True)


def get_wikititles(tokens, maps):
    '''
    获取所有token中出现次数最多的token，返回对应的wikititletag，和是否为直接链接
    :param tokens:
    :param maps:
    :return:
    '''
    # 取出现次数最多的token
    if len(tokens) == 1:
        token = tokens.keys()[0]
    else:
        token = sorted(tokens.items(), key=lambda x: x[1], reverse=True)[0][0]

    # 获取对应的wikititle

    if token in maps['Map_token2wikititles_direct']:
        # logging.info('%s in Map_token2wikititles_direct', token)
        wikititles = maps['Map_token2wikititles_direct'][token]
        is_direct = True
    elif token in maps['Map_token2wikititles_indirect']:
        # logging.info('%s in Map_token2wikititles_indirect', token)
        wikititles = maps['Map_token2wikititles_indirect'][token]
        is_direct = False
    else:
        raise ValueError, 'token: %s, is not in maps' % token

    if len(wikititles) == 1:
        wikititle = wikititles.keys()[0]
    else:
        logging.debug('wikititles length greater than 1, %s', str(wikititles))
        wikititle = sorted(wikititles.items(), key=lambda x: x[1], reverse=True)[0][0]

    # TODO 没有判断是直接链接还是间接链接
    return wikititle, is_direct


def check_bracket(text, x, y, match_group):
    '''
    检查x-y位置在text中是否在[[ ]]或[[[ ]]]标记内部或外部
    在[[ ]]和[[[ ]]]标记外部返回0，在[[ ]]内部返回-1，在[[[ ]]]内部返回1和]]]的位置
    :param text:
    :param y:
    :return: 不在[[ ]][[[ ]]]标签内返回0，在[[[ ]]]内部返回1，其他情况都是不能替换返回-1
    '''
    # 先去x左侧的词块和y右侧的词块,各取300个词
    if x > 300:
        left_block = text[0][x - 300:x]
    else:
        left_block = text[0][:x]
    left_block = left_block[::-1]  # 倒叙排列,因为所有结束标记的时候从x开始
    right_block = text[0][y:y + 300]
    # 查找左右出现[[和]]的位置
    left_brance2_start = left_block.find(r'[[')
    # left_brance2_end = left_block.find(r']]')
    right_brance2_start = right_block.find(r'[[')
    right_brance2_end = right_block.find(r']]')
    left_vertical = left_block.find(r' | ')
    right_vertical = right_block.find(r' | ')
    # 各种情况的优先级
    # 一.在[[ ]]内部,直接返回 -1
    # 二.在[[[ ]]]内部有两种情况:
    #    1.在 | 左侧,返回-1;
    #    2.在 | 右侧,有两种情况:1.是全部的词,返回-1;
    #                         2.是部分词,返回1 和 }} 的位置(为了插入[[[[ ]]]]标记 )
    #    3.是内部的所有词,返回-1
    #    4.是内部部分词,返回1和}}位置(为了插入[[[[ ]]]]标记 )
    # 三.不在[[ ]]和[[[ ]]]内部,返回0
    # print '------------------'
    # print match_group
    # 此处排除在 [[ ]] 和 [[[[ ]]]]标记内, 直接返回-1
    if 0 <= right_brance2_end < right_brance2_start or \
         right_brance2_start < 0 <= right_brance2_end:
        # 这种情况是: word ... ]] , 但是 ]] 不能确定是 ]]] 还是 ]]]]
        # 如果是 ]] 或 ]]]] 直接返回0
        if text[0][y+right_brance2_end+2:y+right_brance2_end+4] == r']]':
            # print '这个是在[[[[ ]]]]内部的'
            return -1, None
        elif text[0][y+right_brance2_end+2:y+right_brance2_end+3] == r']':
            # print '这个是在[[[ ]]]内部的'
            if right_brance2_end > right_vertical >= 0:
                # [[[ xy | ]]]
                # print '[[[ xy | ]]]'
                return -1, None
            elif left_brance2_start > left_vertical >= 0:
                # [[[ | xy]]]
                # print '[[[| xy ]]]'
                # print '|到x的距离: %d' % left_vertical
                # print 'y到}}的距离: %d' % right_brance2_end
                if left_vertical <= 2 and right_brance2_end <= 2:
                    # print '是全部的词'
                    return -1, None
                else:
                    # print '是部分词'
                    return 1, right_brance2_end + 3
            else:
                # [[[ xy ]]]
                # print '[[[ xy ]]]'
                # print '[[[到x的距离: %d' % left_brance2_start
                # print 'y到]]]的距离: %d' % right_brance2_end

                if left_brance2_start <= 2 and right_brance2_end <= 2:
                    # print '是全部的词'
                    return -1, None
                else:
                    # print '是部分词'
                    # print 'start------是部分词'
                    # print text[0][x-left_brance2_start-2:y+right_brance2_end+2]
                    # print match_group
                    # print 'y: %s, right_brance2_end: %s' % (y, right_brance2_end)
                    # print 'end--------是部分词'
                    return 1, right_brance2_end + 3
        else:
            # print '这个是在[[ ]]内部的'
            return -1, None

    return 0, None


def replace_title_link(text, title):
    re_tag = []
    for w in title.lower().split(' '):
        re_tag.append(config.re_word_base.format(re.escape(w)))
    re_lemma = re.compile(r' +'.join(re_tag) + r'\s')
    # print r' +'.join(re_tag)
    # 查找所有匹配
    matchIter = re_lemma.finditer(text[0])
    # 组装替换列表
    last_diff = 0
    replace_list = []
    for match in matchIter:
        x, y = match.span()
        y -= 1
        # print match.group()

        status, pos = check_bracket(text, x, y, match.group())
        # print 'x: %s, y: %s' % (x, y)
        # print 'status: %s, pos: %s\n' % (status, pos)
        if status == 0:
            # 链接在括号外，可直接添加标记
            replace_word = match.group(0)[:-1]
            replace_word = '[[[ {} ]]]'.format(replace_word)
            # print 'replace_word'
            # print replace_word
            match_length = y - x
            replace_length = len(replace_word)
            replace_list.append([x + last_diff, y + last_diff, replace_word])
            last_diff = last_diff + replace_length - match_length
        elif status == 1:
            # 在[[[ ]]]内部
            replace_word = match.group(0)[:-1]
            replace_word = ' [[[[ {} ]]]]'.format(replace_word)
            # print 'replace_word'
            # print replace_word
            replace_length = len(replace_word)
            replace_list.append([y + pos + last_diff, y + pos + last_diff, replace_word])
            last_diff += replace_length
        else:
            # 跳过
            continue

    for i in replace_list:
        text[0] = ''.join((text[0][:i[0]], i[2], text[0][i[1]:]))


def replace_link(text, maps):
    '''
    根据映射表，扩展文中为标记的概念
    :param text:
    :param maps:
    :return:
    '''
    # 替换思路，先将原来的链接隐藏起来（用 ~~~~编号~~~~ 编号为该链接在映射表中的位置），再显示出来
    # 组装每个链接的正则表达式
    for index, link_map in enumerate(maps['Map_lemme2tokens']):
        with DumpRunTime(link_map[0]):
            # 组装匹配lemma的正则
            re_tag = []
            for w in link_map[0].split(' '):
                re_tag.append(config.re_word_base.format(re.escape(w)))
            re_lemma = re.compile(r' +'.join(re_tag) + r'\s')
            # print r' +'.join(re_tag) + r'\s'
            logging.debug('%s', r' +'.join(re_tag) + r'\s')
            # 查找所有匹配
            matchIter = re_lemma.finditer(text[0])
            # 组装替换列表
            last_diff = 0
            replace_list = []
            # print '**********replace_link************'
            # print 'Map_lemme2tokens: %s' % link_map[0]
            # print r' +'.join(re_tag) + r'\s'
            with DumpRunTime('match'):
                start_time = default_timer()
                for match in matchIter:
                    with DumpRunTime('matchIter'):
                        x, y = match.span()
                        y -= 1  # 因为 \s 在结尾处多匹配了一个字符
                        status, pos = check_bracket(text, x, y, match.group())
                        # print 'status: %s, pos: %s' % (status, pos)
                        logging.debug('x: %s, y: %s, last_diff: %s' % (x, y, last_diff))
                        if status == 0:
                            # 链接在括号外，可直接添加标记
                            replace_word, is_direct = get_wikititles(link_map[1], maps)
                            # print 'is_direct: %s' % is_direct
                            if is_direct:
                                replace_word = '[[[ {} ]]]'.format(replace_word)
                            else:
                                replace_word = '[[[ {} | {} ]]]'.format(replace_word, match.group().strip())
                            # print 'replace_word'
                            # print replace_word
                            match_length = y - x
                            replace_length = len(replace_word)
                            replace_list.append([x + last_diff, y + last_diff, replace_word])
                            last_diff = last_diff + replace_length - match_length
                        elif status == 1:
                            # 在[[[ ]]]内部
                            # print '----------replace_link------------'
                            # print match.group()
                            replace_word, is_direct = get_wikititles(link_map[1], maps)
                            # print 'is_direct: %s' % is_direct
                            if is_direct:
                                replace_word = ' [[[[ {} ]]]]'.format(replace_word)
                            else:
                                replace_word = ' [[[[ {} | {} ]]]]'.format(replace_word, match.group().strip())
                            # print 'replace_word'
                            # print replace_word
                            replace_length = len(replace_word)
                            replace_list.append([y + pos + last_diff, y + pos + last_diff, replace_word])
                            last_diff += replace_length
                        else:
                            # 跳过
                            continue

                        # 优化规则,减小正则匹配次数
                        # 检测后面有没有按顺序出现所有lemma
                        match_all = True
                        last_match = y
                        for i in link_map[0].split(' '):
                            last_match = text[0][last_match:].find('/{} '.format(i))
                            if last_match < 0:
                                match_all = False
                                break
                        if match_all == False:
                            break

                    use_time = default_timer() - start_time
                    logging.debug('匹配一个词的,用时 %.4f', use_time)
                    start_time = default_timer()
                use_time = default_timer() - start_time
                logging.debug('匹配一个词的,这是最后一个,用时 %.4f', use_time)

            with DumpRunTime('replace_list'):
                for i in replace_list:
                    # print i
                    text[0] = ''.join((text[0][:i[0]], i[2], text[0][i[1]:]))


def Parse(file, output_directory, reduce_page_number, process_start_time):
    # 打开文件
    if type(file) == list:
        filename = file[1]
        logging.info("start extract file: %s", filename)
        input = fileinput.FileInput('{}/{}'.format(file[0], filename))
        # 创建保存文件
        out = open('{}/{}'.format(output_directory, filename), 'wb')

    else:
        filename = file.split('/')[-1]
        logging.info("start extract file: %s", filename)
        input = fileinput.FileInput(file)
        # 创建保存文件
        out = open('{}/{}'.format(output_directory, filename), 'wb')

    link_maps = {}  # 保存当前文件中所有文章的link_map,用文章的title作为key
    # 读取文件，每次取出一个doc
    start_reduce_time = default_timer()
    for page_data in pages_from(input):
        # 将取出的文件解开
        id, title, url, text = page_data
        text = [text]  # 参数传递改为地址传参
        logging.info("id: %s, title: %s", id, title)

        #  文本的合法性检查：检查是否存在 {{ 或 }} 标记，有的话不处理
        # with DumpRunTime('checkNorm'):
        #     result = checkNorm(text)
        #     if result:
        #         logging.error("the text have error token: %s", str(result))
        #         continue

        # 处理一些特殊字符
        with DumpRunTime('normalize'):
            normalize(text)

        # 映射表
        maps = {
            'Map_lemme2tokens': {},
            'Map_token2wikititles_direct': {},
            'Map_token2wikititles_indirect': {}
        }

        # 创建词原形到概念的映射表
        with DumpRunTime('build_link_map'):
            build_link_map(text, maps)

        # 添加标题的链接
        with DumpRunTime('replace_title_link'):
            replace_title_link(text, title)

        link_maps[title] = {
            'id': id,
            'title': title,
            'Map_lemme2tokens': maps['Map_lemme2tokens'],
            'Map_token2wikititles_direct': maps['Map_token2wikititles_direct'],
            'Map_token2wikititles_indirect': maps['Map_token2wikititles_indirect']
        }
        # for i in maps['Map_lemme2tokens']:
        #     print '---------------'
        #     print i[0]
        #     print i[1]
        # 根据映射表替换文中没有添加的概念
        if maps['Map_lemme2tokens']:
            with DumpRunTime('replace_link'):
                replace_link(text, maps)
        else:
            logging.info('Map_lemme2tokens of %s is None in %s', title, filename)

        # 写入文件
        with DumpRunTime('write_file'):
            line = ['<doc id="%s" url="%s" title="%s">\n' % (id, url, title), text[0], "</doc>\n"]
            out.writelines(line)

        del text, page_data
        use_reduce_time = default_timer() - start_reduce_time
        # 用时大于1秒的报告
        if use_reduce_time > 1:
            logging.info("reduce '{}' use {:.3f} time".format(title, use_reduce_time))
        start_reduce_time = default_timer()

        # 1000次报告一次当前进度
        reduce_page_number.value += 1
        if reduce_page_number.value % config.REPORT_NUM == 0:
            total_time = default_timer() - process_start_time
            reduce_rate = reduce_page_number.value / total_time
            logging.info("Process %d articles, total time %.2fs ( %.2f art/s )", reduce_page_number.value,
                         total_time, reduce_rate)

    # 将映射表保存到文件
    with DumpRunTime('save_link_map'):
        with open('{}/{}_link_maps'.format(config.links_map_directory, filename), 'w') as f:
            pickle.dump(link_maps, f)

    del link_maps

    # 关闭保存的文件
    out.close()
    # 读取完毕，关闭文件
    input.close()


def extract_process(i, files_queue, output_directory, reduce_page_number, process_start_time):
    while True:
        file = files_queue.get()
        logging.info('extract_process files_queue size: %s', files_queue.qsize())
        if file:
            Parse(file, output_directory, reduce_page_number, process_start_time)
        else:
            logging.info("the file gotten from files_queue is 'None', so to quit...")
            logging.debug('Quit extractor')
            break


def main():
    parser = argparse.ArgumentParser(prog=os.path.basename(sys.argv[0]),
                                     formatter_class=argparse.RawDescriptionHelpFormatter,
                                     description=__doc__)
    parser.add_argument("input",
                        help="directory for input files")
    parser.add_argument("-o", "--output", default="output_text",
                        help="directory for extracted files")
    groupS = parser.add_argument_group('Special')
    groupS.add_argument("-q", "--quiet", action="store_true",
                        help="suppress reporting progress info")
    groupS.add_argument("--debug", action="store_true",
                        help="print debug info")
    default_process_count = cpu_count()
    parser.add_argument("--processes", type=int, default=default_process_count,
                        help="Number of processes to use (default %(default)s)")
    groupS.add_argument("-f", "--filesingle", action="store_true",
                        help="analyze a single file outputted by WikiExtractor(debug option)")
    args = parser.parse_args()

    input_directory = args.input
    output_directory = args.output
    process_number = args.processes

    # 配置日志
    if config.log2file:
        logging.basicConfig(format=config.FORMAT, filename=config.log2file)
    else:
        logging.basicConfig(format=config.FORMAT)
    logger = logging.getLogger()
    if not args.quiet:
        logger.setLevel(logging.INFO)
    if args.debug:
        logger.setLevel(logging.DEBUG)

    if not os.path.isdir(args.output):
        try:
            os.makedirs(args.output)
        except:
            logging.error('Could not create: %s', output_directory)
            return

    # 保存映射表的位置
    if not os.path.isdir(config.links_map_directory):
        try:
            os.makedirs(config.links_map_directory)
        except:
            logging.error('Could not create: %s', config.links_map_directory)
            return

    # 创建保存处理文档大小的共享变量
    reduce_page_number = Value('I', 0)
    process_start_time = default_timer()

    # DEBUG模式，只处理一个文件
    if args.filesingle:
        logger.info('Enter Single File mode ...')
        if not os.path.isfile(input_directory):
            logger.error('Single file mode, But the input is not a file!')
            return
        Parse(input_directory, output_directory, reduce_page_number, process_start_time)
        return

    # 记录开始处理的时间
    extract_start = default_timer()

    # 创建保存文件的队列
    maxsize = 10 * process_number
    files_queue = Queue(maxsize=maxsize)

    # 创建处理文件的进程
    worker_count = max(1, process_number)
    workers = []
    for i in range(worker_count):
        extractor = Process(target=extract_process,
                            args=(i, files_queue, output_directory, reduce_page_number, process_start_time))
        extractor.daemon = True
        extractor.start()
        workers.append(extractor)

    # 读取所有文件，保存到文件队列中
    for filename in files_from(input_directory):
        logging.info('Get a file [%s] into the files_queue', filename)
        files_queue.put([input_directory, filename])

    # 向队列中传入结束信号
    logging.info("None is passed to the files_queue to tell the process to exit")
    for _ in workers:
        files_queue.put(None)

    # 等待处理文件的进程结束
    for w in workers:
        w.join()

    # 计算运行时间
    extract_duration = default_timer() - extract_start
    extract_rate = reduce_page_number.value / extract_duration
    logging.info("Finished %d-process extraction of %d articles in %.1fs (%.1f art/s)",
                 process_number, reduce_page_number.value, extract_duration, extract_rate)


if __name__ == '__main__':
    main()
