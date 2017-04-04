# -*- coding: utf-8 -*-
import argparse
import fileinput
import sys
import time
import re
import os
import pickle
import logging
from multiprocessing import Process, Queue

from multiprocessing import Value

if sys.platform == "win32":
    # On Windows, the best timer is time.clock()
    default_timer = time.clock
else:
    # On most other platforms the best timer is time.time()
    default_timer = time.time

docRE = re.compile(r'<doc id="(\d+)" url="(.*?)" title="(.*?)">')
tagRE = re.compile(r'<[^>]+>', re.S)

# 提取[[和]]之间的内容，并且内容中不能包含[[
linkRE = re.compile(r'\[\[((?:(?!\]\])(?!\[\[).)+)\]\]')

# 提取 word1/word2/word3 中的word2和word3，建立词原形到概念的映射
AttiProRE = re.compile(r'[\w\.\'"\-,\|:]+\/[\w\.\'"\-,\|:]+\/([\w\.\'"\-,\|:]+)')

re_word_base = r'[\w\.\'"\-,\|:]+\/[\w\.\'"\-,\|:]+\/{}'

# testRE = re.compile(r'[\w\.\'"\-,\|:\(\)]+')
testRE = re.compile(r'([^\/\s]+\/?)+')

checkNested = re.compile(r'\[\s?\w+:[^\[\]]+\[\[')

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
            logging.info('[%s] run time is %.4fs', self.tag, use_time)
        else:
            logging.error('[Exit %s]: Exited with %s, %s.', self.tag, str(exc_type), str(exc_value))


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
    if " | " in link_block:
        res = map(lambda x:x.strip(), link_block.split(" | "))
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
    links = linkRE.findall(text[0])
    links = list(set(links)) # 去掉重复的链接
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
                    logging.debug("Found a link without source, this link is %s", str(link))
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

    # 替换思路，先将原来的链接隐藏起来（用 ~~~~编号~~~~ 编号为该链接在映射表中的位置），再显示出来
    # 组装每个链接的正则表达式
    try:
        for index, link_map in enumerate(links_map):
            # 减小循环次数，使用python内置字符串替换方法
            text[0] = text[0].replace('[[{}]]'.format(link_map['link_source']), '~~~~{}~~~~'.format(index))
    except Exception as e:
        logging.error("%s, links_map is %s", e, str(links_map))
        sys.exit()

    # 这一步的前提时要现将原文中所有的链接都隐藏以后再执行
    # 替换文中机器添加标记的单词
    replace_total = 0
    for index, link_map in enumerate(links_map):
        # 组装正则表达式
        link_map_match_type = type(link_map['match'])
        if link_map_match_type == list:
            # 组装查找正则表达式
            re_word = []
            for i in range(len(link_map['match'])):
                re_word.append(re_word_base.format(re.escape(link_map['match'][i])))
            re_words = r'\s+'.join(re_word)
            re_str = re_words+r'([^-\w])' # [^-\w] 不能去掉，为了检查单词边界的
        elif link_map_match_type == str:
            re_str = r'({})'.format(re.escape(link_map['match']))
        else:
            logging.error("Unknown link_map_match_type type. link_map:%s", str(link_map))
            continue

        # 开始替换
        # match = re.search(re_str, text)
        # print(re_str)
        # if match:
        # 在text中依次查找link各个单词，每个单词从上一个的位置开始查找
        match_all = True
        last_match = 0
        for i in link_map['match']:
            last_match = text[0][last_match:].find('/'+i)
            if last_match < 0:
                match_all = False
                break
        if match_all:
            text[0], number = re.subn(re_str, r'====' + str(index) + r'====\1', text[0])
            replace_total += number

    # 将原先隐藏的内容重新显示
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
        text[0] = text[0].replace(re_str_r, replace_str_r)
        text[0] = text[0].replace(re_str_j, replace_str_j)

    # logging.info("Add %s links", replace_total)
    # return text


def Parse(file, output_path, reduce_page_number, process_start_time):
    # 打开文件
    if type(file) == list:
        logging.info("start extract file: %s", file[1])
        input = fileinput.FileInput('{}/{}'.format(file[0], file[1]))
        # 创建保存文件
        # out = open('{}/{}'.format(output_path, file[1]), 'w')
    else:
        logging.info("start extract file: %s", file)
        input = fileinput.FileInput(file)
        # 创建保存文件
        out = open('{}/{}'.format(output_path, file.split('/')[-1]), 'w')

    saver = {'title': [], 'link': []}

    # 读取文件，每次取出一个doc
    for page_data in pages_from(input):
        # 将取出的文件解开
        id, title, url, text = page_data

        # saver['title'].append(title)
        #
        # links = linkRE.findall(text)
        # saver['link'].extend(links)
        # reduce_page_number.value += 1

        # find = checkNested.findall(text)
        # if find:
        #     logging.info('file: %s, id: %s, title: %s', file[1], id, title)
        #     for i in find:
        #         logging.info(i)

        # words = testRE.findall(title)
        # reduce_page_number.value += 1
        # try:
        #     assert words, "Don't match id:%s, title:%s, file:%s" % (id, title, input.filename())
        #     match_title = ' '.join(words)
        #     # print "title:%s\tmatch_title:%s" % (title, match_title)
        #     assert title == match_title, 'Match error id:%s, title:%s, match title:%s, file:%s' % (id, title, str(words), input.filename())
        # except AssertionError as e:
        #     print e
        #     sys.exit()
    # pickle.dump(saver, out)

    # 关闭保存的文件
    # out.close()
    # 读取完毕，关闭文件
    input.close()


def extract_process(i, files_queue, output_path, reduce_page_number, process_start_time):
    while True:
        file = files_queue.get()
        logging.info('extract_process files_queue size: %s', files_queue.qsize())
        if file:
            Parse(file, output_path, reduce_page_number, process_start_time)
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

    # FORMAT = 'PID:%(process)d - %(levelname)s [%(lineno)d]: [%(funcName)s] %(message)s'
    FORMAT = 'PID:%(process)d - %(levelname)s: %(message)s'
    logging.basicConfig(format=FORMAT,filename='2step.log')
    # logging.basicConfig(format=FORMAT)
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

    input_directory = args.input
    output_directory = args.output
    process_number = args.processes

    # 创建保存处理文档大小的共享变量
    reduce_page_number = Value('I', 0)
    process_start_time = default_timer()

    if args.filesingle:
        logger.info('Enter Single File mode ...')
        input_file = input_directory
        output_file = output_directory
        if not os.path.isfile(input_file):
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