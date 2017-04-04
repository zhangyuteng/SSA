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

from multiprocessing import Value, Array

if sys.platform == "win32":
    # On Windows, the best timer is time.clock()
    default_timer = time.clock
else:
    # On most other platforms the best timer is time.time()
    default_timer = time.time

docRE = re.compile(r'<doc id="(\d+)" url="(.*?)" title="(.*?)">')
tagRE = re.compile(r'<[^>]+>', re.S)

# 提取[[和]]之间的内容，并且内容中不能包含[[
ManualLinkRE = re.compile(r'\[\[\s?((?:(?!\[\[).)+)\s?\]\]')

# 提取{{和}}之间的内容，并且内容中不能包含{{
RobotlLinkRE = re.compile(r'\{\{[^}]+\}\}')

# 提取 word1/word2/word3 中的word2和word3，建立词原形到概念的映射
AttiProRE = re.compile(r'[\w\.\'"\-,]+\/[\w\.\'"\-,\|]+\/([\w\.\'"\-,]+)')

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


def build_links(text, links):
    # 提取人工添加的链接
    manualLinks = ManualLinkRE.findall(text[0])
    manualLinks = list(set(manualLinks))  # 去掉重复的链接
    print(len(manualLinks))
    for link, link_block in map(extract_link_block,manualLinks):
        if link:
            length_link = len(link)
            if length_link == 1:
                if link[0] in links:
                    links[link[0]][link[0]]['manual'] += 1
                else:
                    links[link[0]] = {link[0]: {'manual': 1, 'robot': 0}}

            elif length_link == 2:
                if link[1] in links:
                    if link[1] in links[link[0]]:
                        links[link[0]][link[1]]['manual'] += 1
                    else:
                        links[link[0]][link[1]] = {'manual': 1, 'robot': 0}
                else:
                    links[link[1]] = {link[0]: {'manual': 1, 'robot': 0}}

            else:
                logging.error("manual link have a Not standard: %s", str(link_block))
                continue
    # 提取机器添加的链接
    robotLinks = RobotlLinkRE.findall(text[0])
    robotLinks = list(set(robotLinks))
    print(len(robotLinks))
    text[0] = None


def extract_process(i, files_queue, output_path, reduce_page_number, process_start_time):
    while True:
        file = files_queue.get()
        logging.info('extract_process files_queue size: %s', files_queue.qsize())
        if file:
            logging.info("start extract file: %s", file[1])
            # 保存链接数据
            links = set()
            # 打开文件
            input = fileinput.FileInput('{}/{}'.format(file[0], file[1]))
            # 创建保存文件
            # out = open('{}/{}'.format(output_path, file[1]), 'w')
            # 读取文件，每次取出一个doc
            start_reduce_time = default_timer()
            for page_data in pages_from(input):
                # 将取出的文件解开
                id, title, url, text = page_data
                logging.info("id: %s, title: %s", id, title)


                with DumpRunTime('build_links'):
                    text = [text] # 将text改成引用传参
                    build_links(text, links)


                del text, page_data
                use_reduce_time = default_timer() - start_reduce_time
                # 用时大于1秒的报告
                if use_reduce_time > 1:
                    logging.info("reduce '{}' use {:.3f} time".format(title, use_reduce_time))
                start_reduce_time = default_timer()

                # 1000次报告一次当前进度
                reduce_page_number.value += 1
                if reduce_page_number.value % 1000 == 0:
                    total_time = default_timer() - process_start_time
                    reduce_rate = reduce_page_number.value / total_time
                    logging.info("Process %d articles, total time %.2fs ( %.2f art/s )", reduce_page_number.value,
                                 total_time, reduce_rate)
            # 关闭保存的文件
            # out.close()
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

    # FORMAT = 'PID:%(process)d - %(levelname)s [%(lineno)d]: [%(funcName)s] %(message)s'
    FORMAT = 'PID:%(process)d - %(levelname)s: %(message)s'
    # logging.basicConfig(format=FORMAT,filename='2step.log')
    logging.basicConfig(format=FORMAT)
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

    # 创建保存处理文档大小的共享变量
    reduce_page_number = Value('I', 0)
    process_start_time = default_timer()

    # 创建处理文件的进程
    worker_count = max(1, args.processes)
    workers = []
    for i in range(worker_count):
        extractor = Process(target=extract_process,
                            args=(i, files_queue, args.output, reduce_page_number, process_start_time))
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
    extract_rate = reduce_page_number.value / extract_duration
    logging.info("Finished %d-process extraction of %d articles in %.1fs (%.1f art/s)",
                 args.processes, reduce_page_number.value, extract_duration, extract_rate)


if __name__ == '__main__':
    main()
