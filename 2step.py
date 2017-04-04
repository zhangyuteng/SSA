# -*- coding: utf-8 -*-
import argparse
import fileinput
import random
import re
import pickle
import logging
from multiprocessing import Process, Queue
from multiprocessing import Value
from util.basic import *
import config

__version__ = '2017040402'


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


def build_link_map_old(text):
    '''
    提取文章中人工标注的链接
    :param text:
    :return:
    '''
    links_map = []
    # text是一个string
    links = config.linkRE.findall(text[0])
    links = list(set(links))  # 去掉重复的链接
    if links:
        for link, link_source in map(extract_link_block, links):
            if not link:
                continue
            # link 中有一个item时，[0]:链接指向本身
            # link 中有两个item时，[0]:指向的目标，[1]:链接的名称
            link_num = len(link)
            if link_num == 1:
                # 这是只有链接是本身的情况
                word = config.AttiProRE.findall(link[0])
                if word:
                    item = {
                        'match': word,  # 需要匹配的部分，是一个列表
                        'match_word_num': len(word),
                        'source': link,  # 处理过的链接的原形
                        'link_source': link_source,  # 为处理过的链接原形
                        'target': None  # 链接的目标，None表示本身
                    }
                else:
                    # 可能无法用 / 分开，所以用所有词
                    item = {
                        'match': link[0],  # 需要匹配的部分，是一个字符串
                        'match_word_num': link[0].count(' ') + 1,
                        'source': link,  # 处理过的链接的原形
                        'link_source': link_source,  # 为处理过的链接原形
                        'target': None  # 链接的目标，None表示本身
                    }
                links_map.append(item)
            elif link_num == 2:
                # 排除 [[ Category:Anarchism | ]] 这种情况
                if not link[1]:
                    logging.debug("Found a link without source, this link is %s", str(link))
                    continue
                # 这是链接到其他的概念
                word = config.AttiProRE.findall(link[1])
                if word:
                    item = {
                        'match': word,  # 需要匹配的部分，是一个列表
                        'match_word_num': len(word),
                        'source': link,  # 处理过的链接的原形
                        'link_source': link_source,  # 为处理过的链接原形
                        'target': link[0]  # 链接的目标，None表示本身
                    }
                else:
                    item = {
                        'match': link[1],  # 需要匹配的部分，是一个字符串
                        'match_word_num': link[0].count(' ') + 1,
                        'source': link,  # 处理过的链接的原形
                        'link_source': link_source,  # 为处理过的链接原形
                        'target': link[0]  # 链接的目标，None表示本身
                    }
                links_map.append(item)
            else:
                logging.error("There are multiple '|' in the link, please check. link: %s", str(link))
        # 将映射表按照match中单词长度倒序排列
        return sorted(links_map, key=lambda x: x['match_word_num'], reverse=True)


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
    检查x-y位置在text中是否在[[ ]]或{{ }}标记内部或外部
    在[[ ]]和{{ }}标记外部返回0，在[[ ]]内部返回-1，在{{ }}内部返回1和}}的位置
    :param text:
    :param y:
    :return: 不在[[ ]]和{{ }}标签内返回0，在{{ }}内部返回1，其他情况都是不能替换返回-1
    '''
    # 先去x左侧的词块和y右侧的词块,各取300个词
    if x > 300:
        left_block = text[0][x - 300:x]
    else:
        left_block = text[0][:x]
    left_block = left_block[::-1]  # 倒叙排列,因为所有结束标记的时候从x开始
    right_block = text[0][y:y + 300]
    # 计算长度
    left_block_length = len(left_block)
    right_block_length = len(right_block)
    # 查找左右出现[[和]]的位置
    left_brance1_start = left_block.find(r'[[')
    left_brance1_end = left_block.find(r']]')
    right_brance1_start = right_block.find(r'[[')
    right_brance1_end = right_block.find(r']]')
    # 查找左右出现{{和}}的位置
    left_brance2_start = left_block.find(r'{{')
    left_brance2_end = left_block.find(r'}}')
    right_brance2_start = right_block.find(r'{{')
    right_brance2_end = right_block.find(r'}}')
    # 查找|出现的位置
    left_vertical = left_block.find(r' | ')
    right_vertical = right_block.find(r' | ')
    # 各种情况的优先级
    # 一.在[[ ]]内部,直接返回 -1
    # 二.在{{ }}内部有两种情况:
    #    1.在 | 左侧,返回-1;
    #    2.在 | 右侧,有两种情况:1.是全部的词,返回-1;
    #                         2.是部分词,返回1 和 }} 的位置(为了插入{{{ }}}标记 )
    #    3.是内部的所有词,返回-1
    #    4.是内部部分词,返回1和}}位置(为了插入{{{ }}}标记 )
    # 三.不在[[ ]]和{{ }}内部,返回0
    if right_brance1_start > right_brance1_end >= 0 or \
        right_brance1_end >= 0 > right_brance1_start:
        # 在[[ ]]内部,直接返回 -1
        return -1, None

    if right_brance2_start > right_brance2_end >= 0 or \
        right_brance2_end >= 0 > right_brance2_start:
        # 在{{ }}内部
        # print '\n在{{ }}内部'
        # print '*********************'
        # print match_group
        # print '*********************'
        # print text[0][x-left_brance2_start-2:y + right_brance2_end+2]
        # print '*********************'
        if right_brance2_end > right_vertical >= 0:
            # {{ xy | }}
            # print '{{ xy | }}'
            return -1, None
        elif left_brance2_start > left_vertical >= 0:
            # {{ | xy }
            # print '{{ | xy }}'
            # print '|到x的距离: %d' % left_vertical
            # print 'y到}}的距离: %d' % right_brance2_end
            if left_vertical <=2 and right_brance2_end <= 2:
                # 是全部的词
                return -1, None
            else:
                # 是部分词
                return 1, right_brance2_end+2
        else:
            # {{ xy }}
            # print '{{ xy }}'
            # print '{{到x的距离: %d' % left_brance2_start
            # print 'y到}}的距离: %d' % right_brance2_end

            if left_brance2_start <=2 and right_brance2_end <= 2:
                # 是全部的词
                return -1, None
            else:
                # 是部分词
                # print 'start------是部分词'
                # print text[0][x-left_brance2_start-2:y+right_brance2_end+2]
                # print match_group
                # print 'y: %s, right_brance2_end: %s' % (y, right_brance2_end)
                # print 'end--------是部分词'
                return 1, right_brance2_end+2
    else:
        # print match_group
        # print '这是未在{{ }} [[ ]]内部的匹配'
        return 0, None

    # start_1 = text[0][y:300].find(r'[[')
    # end_1 = text[0][y:300].find(r']]')
    # if start_1 > end_1 >= 0 or end_1 >= 0 > start_1:
    #     # 在[[ ]]内部
    #     return -1, None
    # # elif start_1 >= 0 > end_1:  # 这里不对了,因为支取了300个词
    # #     # 出现[[ ... 未闭合的情况
    # #     logging.error('Find the unclosed label at [[ ]], y: %s', y)
    # #     return -1, None
    #
    # # 上面的判断做完后能够保证token在[[ ]]外，但是不能保证是否在{{ }}的范围
    # start_2 = text[0][y:].find(r'{{')
    # end_2 = text[0][y:].find(r'}}')
    # if end_2 > start_2 >= 0 or start_2 == end_2 == -1 or start_2 >= 0 > end_2:
    #     # 在{{ }}外部，同时也在[[ ]]外部
    #     return 0, None
    # elif start_2 > end_2 >= 0 or end_2 >= 0 > start_2:
    #     # 在{{ }}内部，还需要判断当前匹配的token是否是词块的全部，如果是全部就不用在外部添加{{{ }}}，否则添加。
    #     # 倒叙查找{{
    #     # print '--------check_bracket---------'
    #     # TODO 这里需要验证下，是否有超过300个字符的链接词
    #     if y > 300:
    #         temp = text[0][y - 300:y]
    #     else:
    #         temp = text[0][:y]
    #     # print type(temp), len(temp)
    #     tag_brance = temp[::-1].find('{{')
    #     tag_vertical = temp[::-1].find('|')
    #
    #     if tag_brance > tag_vertical >= 0:
    #         # {{  |  y 这种模式
    #         diff = tag_vertical - (y - x)
    #     elif tag_brance >= 0 > tag_vertical or tag_vertical > tag_brance >= 0:
    #         # {{     y 这种模式    或
    #         # |  {{  y 这种模式
    #         # 此时还需要判断是否为{{ y | 这种模式
    #         # print tag_brance, tag_vertical
    #         vertical = text[0][y:].find(r' | ')
    #         if 0 == vertical:
    #             return -1, None
    #         diff = tag_brance - (y - x)
    #     else:
    #         raise ValueError, '出现未匹配的标签,tag_brance: %s,tag_vertical: %s,x: %s,y: %s' % (tag_brance, tag_vertical, x, y)
    #
    #     # print 'diff: %s' % diff
    #
    #     if diff == 1:
    #         # 机器添加的都是 1
    #         return -1, None
    #     else:
    #         return 1, end_2 + 2
    # else:
    #     logging.error('Find the unclosed label at {{ }}', y)
    #     return -1, None


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
            replace_word = '{{{{ {} }}}}'.format(replace_word)
            match_length = y - x
            replace_length = len(replace_word)
            replace_list.append([x + last_diff, y + last_diff, replace_word])
            last_diff = last_diff + replace_length - match_length
        elif status == 1:
            # 在{{ }}内部
            replace_word = match.group(0)[:-1]
            replace_word = ' {{{{{{ {} }}}}}}'.format(replace_word)
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
                                replace_word = '{{{{ {} }}}}'.format(replace_word)
                            else:
                                replace_word = '{{{{ {} | {} }}}}'.format(replace_word, match.group().strip())
                            match_length = y - x
                            replace_length = len(replace_word)
                            replace_list.append([x + last_diff, y + last_diff, replace_word])
                            last_diff = last_diff + replace_length - match_length
                        elif status == 1:
                            # 在{{ }}内部
                            # print '----------replace_link------------'
                            # print match.group()
                            replace_word, is_direct = get_wikititles(link_map[1], maps)
                            # print 'is_direct: %s' % is_direct
                            if is_direct:
                                replace_word = ' {{{{{{ {} }}}}}}'.format(replace_word)
                            else:
                                replace_word = ' {{{{{{ {} | {} }}}}}}'.format(replace_word, match.group().strip())
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
        # TODO 记得把它解除注释
        # with DumpRunTime('checkNorm'):
        #     result = checkNorm(text)
        #     if result:
        #         logging.error("the text have error token: %s", str(result))
        #         continue

        # 处理一些特殊字符
        with DumpRunTime('normalize'):
            normalize(text)

        # 添加标题的链接
        with DumpRunTime('replace_title_link'):
            replace_title_link(text, title)

        # 映射表
        maps = {
            'Map_lemme2tokens': {},
            'Map_token2wikititles_direct': {},
            'Map_token2wikititles_indirect': {}
        }
        # 创建词原形到概念的映射表
        with DumpRunTime('build_link_map'):
            build_link_map(text, maps)

        link_maps[title] = {
            'id': id,
            'title': title,
            'Map_lemme2tokens': maps['Map_lemme2tokens'],
            'Map_token2wikititles_direct': maps['Map_token2wikititles_direct'],
            'Map_token2wikititles_indirect': maps['Map_token2wikititles_indirect']
        }

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
        if reduce_page_number.value % 100 == 0:
            total_time = default_timer() - process_start_time
            reduce_rate = reduce_page_number.value / total_time
            logging.info("Process %d articles, total time %.2fs ( %.2f art/s )", reduce_page_number.value,
                         total_time, reduce_rate)

    # 将映射表保存到文件
    with DumpRunTime('save_link_map'):
        with open('{}/{}_link_maps'.format(config.links_map_directory, filename), 'w') as f:
            pickle.dump(link_maps, f)

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
    # logging.basicConfig(format=config.FORMAT, filename='2step.log')
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
