# -*- coding: utf-8 -*-
import argparse
import fileinput
import sys
import time
import re
import os
import pickle
import logging
from functools import reduce
from multiprocessing import Process, Queue

if sys.platform == "win32":
    # On Windows, the best timer is time.clock()
    default_timer = time.clock
else:
    # On most other platforms the best timer is time.time()
    default_timer = time.time

docRE = re.compile(r'<doc id="(\d+)" url="(.*?)" title="(.*?)">')
tagRE = re.compile(r'<[^>]+>', re.S)

# 提取[[和]]之间的内容，并且内容中不能包含[[
linkRE = re.compile(r'\[\[\s?((?:(?!\[\[).)*?)\s?\]\]')

# 提取 word1/word2/word3 中的word2和word3，建立词原形到概念的映射
AttiProRE = re.compile(r'\S+\/\S+\/(\S+)')

# 映射表保存位置
links_map_folder = 'links_map'

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
        if os.path.isfile('{}/{}'.format(path,f)):
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
        if in_text:
            if line == '</doc>\n' or line == '</doc>':
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
            m = docRE.search(line)
            if m:
                title = m.group(3)
                id = m.group(1)
                url = m.group(2)
                in_text = True


def extract_link_block(link_block):
    '''
    [[ word ]] 将会解析成 list([word])
    [[ word1 | word2 ]] 将会解析成 list([word1, word2])，word2是在文中显示的词，word1是将会跳转到的词
    :param link_block:
    :return:
    '''
    if "|" in  link_block:
        res = map(lambda x:x.strip(), link_block.split("|"))
    elif link_block.find('Category:') == -1:
        res = [link_block.strip()]
    else:
        # logging.warning("find a Category link_block, that is %s", link_block)
        res = []
    return  list(res), link_block


def build_link_map(text):
    '''
    提取文章中人工标注的链接
    :param text:
    :return:
    '''
    links_map = []
    # text是一个string
    # start_time = default_timer()
    links = linkRE.findall(text)
    links = list(set(links)) # 去掉重复的链接
    # use_time = default_timer() - start_time
    # logging.info("string text re use {:.6f} time".format(use_time))
    # 将text转为长字符串再进行正则 use    0.000150    time
    # 每次处理一行，再合并         use    0.000003    time
    # 结论是使用正则匹配是尽量减小字符串的长度，时间相差50倍
    # text是一个list
    # start_time = default_timer()
    # links = map(linkRE.findall, text)
    # links = sum(links, [])
    # use_time = default_timer() - start_time
    # logging.info("list text re use {:.6f} time".format(use_time))
    if links:
        for link, link_source in map(extract_link_block,links):
            if not link:
                continue
            # link 中有一个item时，[0]:链接指向本身
            # link 中有两个item时，[0]:指向的目标，[1]:链接的名称
            link_num = len(link)
            if link_num == 1:
                # 这是只有链接是本身的情况
                word = AttiProRE.findall(link[0])
                if word:
                    item = {
                        'match': word, # 需要匹配的部分，是一个列表
                        'match_word_num': len(word),
                        'source': link, # 处理过的链接的原形
                        'link_source': link_source, # 为处理过的链接原形
                        'target': None # 链接的目标，None表示本身
                    }
                else:
                    # 可能无法用 / 分开，所以用所有词
                    item = {
                        'match': link[0],  # 需要匹配的部分，是一个字符串
                        'match_word_num': link[0].count(' ') + 1,
                        'source': link,  # 处理过的链接的原形
                        'link_source': link_source, # 为处理过的链接原形
                        'target': None  # 链接的目标，None表示本身
                    }
                links_map.append(item)
            elif link_num == 2:
                # 排除 [[ Category:Anarchism | ]] 这种情况
                if not link[1]:
                    logging.error("Found a link without source, this link is %s", str(link))
                    continue
                # 这是链接到其他的概念
                word = AttiProRE.findall(link[1])
                if word:
                    item = {
                        'match': word,  # 需要匹配的部分，是一个列表
                        'match_word_num': len(word),
                        'source': link,  # 处理过的链接的原形
                        'link_source': link_source, # 为处理过的链接原形
                        'target': link[0]  # 链接的目标，None表示本身
                    }
                else:
                    item = {
                        'match': link[1],  # 需要匹配的部分，是一个字符串
                        'match_word_num': link[0].count(' ') + 1,
                        'source': link,  # 处理过的链接的原形
                        'link_source': link_source, # 为处理过的链接原形
                        'target': link[0]  # 链接的目标，None表示本身
                    }
                links_map.append(item)
            else:
                logging.error("There are multiple '|' in the link, please check. link: %s", str(link))
        # 将映射表按照match中单词长度倒序排列
        return sorted(links_map, key=lambda x: x['match_word_num'], reverse=True)


def replace_link(links_map, text):
    '''
    根据映射表，扩展文中为标记的概念
    :param links_map:
    :param text:
    :return:
    '''
    re_word_base = r'[A-Za-z-]+\/[A-Za-z-]+\/{}'
    # 替换思路，先将原来的链接隐藏起来（用 ~~~~编号~~~~ 编号为该链接在映射表中的位置），再显示出来
    # 组装每个链接的正则表达式
    start_time = default_timer()
    for index, link_map in enumerate(links_map):
        if not link_map['match']:
            continue
        # if index in [415,533]:
        #     print(link_map)
        # 减小循环次数，使用python内置字符串替换方法
        text = text.replace('[[ {} ]]'.format(link_map['link_source']), '~~~~{}~~~~'.format(index))
        # 减小循环次数前的代码
        # link_map_match_type = type(link_map['match'])
        # # print(link_map_match_type)
        # if link_map_match_type == list:
        #     # print(' '.join(link_map['match']))
        #     re_word = []
        #     for i in range(len(link_map['match'])):
        #         re_word.append(re_word_base.format(re.escape(link_map['match'][i])))
        #     # print(re_word)
        #     re_words = r'\s+'.join(re_word)
        #     # print(re_words)
        #     re_str = r'\[\[(?:(?!\]\]).)+{}\s+\]\]'.format(re_words)
        # elif link_map_match_type == str:
        #     # print(link_map['match'])
        #     re_str = r'\[\[(?:(?!\]\]).)*{}\s*\]\]'.format(re.escape(link_map['match']))
        # else:
        #     logging.error("Unknown link_map_match_type type. link_map:%s", str(link_map))
        #     continue
        # # 替换文中人工标注的链接
        # # text is str
        # text = re.sub(re_str, '~~~~'+str(index)+'~~~~', text)
        # # text is list
        # # resub = lambda line: re.sub(re_str, '~~~~' + str(index) + '~~~~', line)
        # # text = map(resub, list(text))
    use_time = default_timer() - start_time
    logging.info("replace_link 1 step use {:.6f} time".format(use_time))

    # 这一步的前提时要现将原文中所有的链接都隐藏以后再执行
    # 替换文中机器添加标记的单词
    replace_total = 0
    start_time = default_timer()
    for index, link_map in enumerate(links_map):
        # print(link_map)
        if not link_map['match']:
            continue
        first_word = ''
        link_map_match_type = type(link_map['match'])
        if link_map_match_type == list:
            first_word = link_map['match'][0]
            # 组装查找正则表达式
            re_word = []
            for i in range(len(link_map['match'])):
                re_word.append(re_word_base.format(re.escape(link_map['match'][i])))
            re_words = r'\s+'.join(re_word)
            re_str = r'('+re_words+')\s+' # \s 不能去掉，为了检查单词边界的
        elif link_map_match_type == str:
            first_word = link_map['match']
            # print(link_map['match'])
            re_str = r'({})'.format(re.escape(link_map['match']))
        else:
            logging.error("Unknown link_map_match_type type. link_map:%s", str(link_map))
            continue
        # 组装要替换的字符串为隐藏属性 ====编号====
        # text is str
        # resub_start_time = default_timer()
        # match = re.search(re_str, text)
        # if match:
        # print(match)
        findres = text.find('/'+first_word)
        if findres > 0:
            # print(re_str)
            text, number = re.subn(re_str, '====' + str(index) + '====', text)
            replace_total += number
            # print("replace {} numbers".format(number))
            # sys.exit()
        # use_time = default_timer() - resub_start_time
        # 打印正则表达式
        # logging.info(re_str)
        # logging.info("replace_link 2 step one link use {:.6f} time".format(use_time))
        # text is list
        # resub = lambda string: re.sub(re_str, '====' + str(index) + '====', string)
        # text = map(resub, list(text))
    use_time = default_timer() - start_time
    logging.info("replace_link 2 step use {:.6f} time".format(use_time))

    # 将原先隐藏的内容重新显示
    start_time = default_timer()
    for index, link_map in enumerate(links_map):
        if not link_map['match']:
            continue
        # 组装原始字符串(要恢复的字符串)
        if link_map['target']:
            # target 有值说明其指向不是自己，所以source字段有两个值，第一个是目标，第二个是原文
            replace_str_r = "[[ {0} | {1} ]]".format(*link_map['source'])
            replace_str_j = "{{{{ {0} | {1} }}}}".format(*link_map['source']) # {{ 写两遍转义为一个{
        else:
            # target 无值说明其指向是自己，所以source字段有一个值，第一个是原文
            replace_str_r = "[[ {} ]]".format(*link_map['source'])
            replace_str_j = "{{{{ {0} }}}}".format(*link_map['source']) # {{ 写两遍转义为一个{
        # 组装查找正则表达式
        re_str_r = '~~~~{}~~~~'.format(index)
        re_str_j = '===={}===='.format(index)

        # 用字符串替换
        # 开始替换
        text = text.replace(re_str_r, replace_str_r)
        text = text.replace(re_str_j, replace_str_j)

        # 用正则替换
        # # 开始替换
        # # text is str
        # text = re.sub(re_str_r, replace_str_r, text)
        # text = re.sub(re_str_j, replace_str_j, text)
        # # text is list
        # # resub_r = lambda string: re.sub(re_str_r, replace_str_r, string)
        # # resub_j = lambda string: re.sub(re_str_j, replace_str_j, string)
        # # text = map(resub_r, text)
        # # text = map(resub_j, text)
    use_time = default_timer() - start_time
    logging.info("replace_link 3 step use {:.6f} time".format(use_time))

    logging.info("Add %s links", replace_total)
    return text


def extract_process(i, files_queue, output_path):
    while True:
        file = files_queue.get()
        logging.info('extract_process files_queue size: %s', files_queue.qsize())
        if file:
            logging.info("start extract file: %s", file[1])
            # 打开文件
            input = fileinput.FileInput('{}/{}'.format(file[0],file[1]))
            # 创建保存文件
            out = open('{}/{}'.format(output_path,file[1]), 'w')
            # 读取文件，每次取出一个doc
            start_reduce_time = default_timer()
            for page_data in pages_from(input):
                # 将取出的文件解开
                id, title, url, text = page_data
                logging.info("Start processing the doc. id: %s, title: %s", id, title)
                # 创建词原形到概念的映射表
                start_time = default_timer()
                cache = '{}/{}'.format(links_map_folder, title)
                if os.path.isfile(cache):
                    logging.info('build_link_map load cache')
                    with open(cache, 'rb') as f:
                        links_map = pickle.load(f)
                else:
                    links_map = build_link_map(text)
                    with open(cache, 'wb') as f:
                        pickle.dump(links_map, f)
                logging.info("links_map size is %s", len(links_map))
                use_time = default_timer() - start_time
                logging.info("build_link_map use {:.6f} time".format(use_time))

                # 根据映射表替换文中没有添加的概念
                start_time = default_timer()
                text = replace_link(links_map, text)
                use_time = default_timer() - start_time
                logging.info("replace_link total use {:.6f} time".format(use_time))

                start_time = default_timer()
                # text is str
                line = '<doc id="%s" url="%s" title="%s">\n' % (id, url, title)
                line += text
                line += "</doc>\n"
                # text is list
                # line = '<doc id="%s" url="%s" title="%s">\n' % (id, url, title)
                # line += ''.join(text)
                # line += "</doc>\n"
                out.write(line)
                use_time = default_timer() - start_time
                logging.info("write file use {:.6f} time".format(use_time))

                del text,page_data
                use_reduce_time = default_timer() - start_reduce_time
                logging.info("reduce '{}' document use {:.6f} time".format(title, use_reduce_time))
                start_reduce_time = default_timer()
            # 关闭保存的文件
            out.close()
            # 读取完毕，关闭文件
            input.close()
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
    args = parser.parse_args()

    FORMAT = 'PID:%(process)d - %(levelname)s [%(lineno)d]: [%(funcName)s] %(message)s'
    logging.basicConfig(format=FORMAT)#,filename='2step.log')
    logger = logging.getLogger()
    if not args.quiet:
        logger.setLevel(logging.INFO)
    if args.debug:
        logger.setLevel(logging.DEBUG)

    if not os.path.isdir(args.output):
        try:
            os.makedirs(args.output)
        except:
            logging.error('Could not create: %s', args.output)
            return
    # 保存映射表
    if not os.path.isdir(links_map_folder):
        try:
            os.makedirs(links_map_folder)
        except:
            logging.error('Could not create: %s', links_map_folder)
            return

    # 记录开始处理的时间
    extract_start = default_timer()

    # 创建保存文件的队列
    maxsize = 10 * args.processes
    files_queue = Queue(maxsize=maxsize)

    # 创建处理文件的进程
    worker_count = max(1, args.processes)
    workers = []
    for i in range(worker_count):
        extractor = Process(target=extract_process,
                            args=(i, files_queue, args.output))
        extractor.daemon = True
        extractor.start()
        workers.append(extractor)

    # 读取所有文件，保存到文件队列中
    for filename in files_from(args.input):
        logging.info('Get a file [%s] into the files_queue', filename)
        files_queue.put([args.input, filename])

    # 向队列中传入结束信号
    logging.info("None is passed to the files_queue to tell the process to exit")
    for _ in workers:
        files_queue.put(None)

    # 等待处理文件的进程结束
    for w in workers:
        w.join()

    # 计算运行时间
    extract_duration = default_timer() - extract_start
    logging.info("Finished %d-process extraction use %1.fs", args.processes, extract_duration)

if __name__ == '__main__':
    main()