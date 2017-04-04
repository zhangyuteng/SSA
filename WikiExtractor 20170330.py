#!/usr/bin/env python
# -*- coding: utf-8 -*-

# =============================================================================
#  Version: 2.66 (Oct 29, 2016)
#  Author: Giuseppe Attardi (attardi@di.unipi.it), University of Pisa
#
#  Contributors:
#   Antonio Fuschetto (fuschett@aol.com)
#   Leonardo Souza (lsouza@amtera.com.br)
#   Juan Manuel Caicedo (juan@cavorite.com)
#   Humberto Pereira (begini@gmail.com)
#   Siegfried-A. Gevatter (siegfried@gevatter.com)
#   Pedro Assis (pedroh2306@gmail.com)
#   Wim Muskee (wimmuskee@gmail.com)
#   Radics Geza (radicsge@gmail.com)
#   orangain (orangain@gmail.com)
#   Seth Cleveland (scleveland@turnitin.com)
#
# =============================================================================
#  Copyright (c) 2011-2016. Giuseppe Attardi (attardi@di.unipi.it).
# =============================================================================
#  This file is part of Tanl.
#
#  Tanl is free software; you can redistribute it and/or modify it
#  under the terms of the GNU General Public License, version 3,
#  as published by the Free Software Foundation.
#
#  Tanl is distributed in the hope that it will be useful,
#  but WITHOUT ANY WARRANTY; without even the implied warranty of
#  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
#  GNU General Public License for more details.
#
#  You should have received a copy of the GNU General Public License
#  along with this program.  If not, see <http://www.gnu.org/licenses/>.
# =============================================================================

"""Wikipedia Extractor:
Extracts and cleans text from a Wikipedia database dump and stores output in a
number of files of similar size in a given directory.
Each file will contain several documents in the format:

    <doc id="" revid="" url="" title="">
        ...
        </doc>

Template expansion requires preprocesssng first the whole dump and
collecting template definitions.
"""

from __future__ import unicode_literals, division

import sys
import argparse
import bz2
import codecs
import cgi
import fileinput
import logging
import os.path
import re  # TODO use regex when it will be standard
import time
from io import StringIO
from multiprocessing import Queue, Process, Value, cpu_count
from timeit import default_timer
#from nltk.corpus import stopwords

PY2 = sys.version_info[0] == 2
if PY2:
    from urllib import quote
    from htmlentitydefs import name2codepoint
    from itertools import izip as zip, izip_longest as zip_longest
    range = xrange  # Overwrite by Python 3 name
    chr = unichr    # Overwrite by Python 3 name
    text_type = unicode
else:
    from urllib.parse import quote
    from html.entities import name2codepoint
    from itertools import zip_longest
    text_type = str


# ===========================================================================

# Program version
version = '2.66'

## PARAMS ####################################################################

##
# Defined in <siteinfo>
# We include as default Template, when loading external template file.
knownNamespaces = set(['Template'])

##
# Keys for Template and Module namespaces
templateKeys = set(['10', '828'])

##
# The namespace used for template definitions
# It is the name associated with namespace key=10 in the siteinfo header.
templateNamespace = ''
templatePrefix = ''

##
# The namespace used for module definitions
# It is the name associated with namespace key=828 in the siteinfo header.
moduleNamespace = ''

##
# Recognize only these namespaces in links
# w: Internal links to the Wikipedia
# wiktionary: Wiki dictionary
# wikt: shortcut for Wiktionary
#
acceptedNamespaces = ['w', 'wiktionary', 'wikt']
acceptedNamespaces_lustyle = ['w', 'wiktionary', 'wikt', 'Category'] #lu makeInternalLink_lustyle() need the list

##
# Drop these elements from article text
#
discardElements = [
    'gallery', 'timeline', 'noinclude', 'pre',
    'table', 'tr', 'td', 'th', 'caption', 'div',
    'form', 'input', 'select', 'option', 'textarea',
    'ul', 'li', 'ol', 'dl', 'dt', 'dd', 'menu', 'dir',
    'ref', 'references', 'img', 'imagemap', 'source', 'small',
    'sub', 'sup', 'indicator'
]

# This is obtained from <siteinfo>
urlbase = ''


# This is by luwpeng
Lustyle = False

##
# Filter disambiguation pages
filter_disambig_pages = False
#filter_disambig_page_pattern = re.compile("{{disambig(uation)?(\|[^}]*)?}}")
filter_disambig_page_pattern = re.compile(r'\{\{[Dd]isambig(uation)?(\|[^\}]*)?\}\}')

##

filter_month_year = re.compile(r'^((January)|(February)|(March)|(April)|(May)|(June)|(July)|(August)|(September)|(October)|(November)|(December)) \d{4}$')
#January 2002
filter_month_day = re.compile(r'^((January)|(February)|(March)|(April)|(May)|(June)|(July)|(August)|(September)|(October)|(November)|(December)) [0123]?\d$')
#January 31
filter_pure_number = re.compile(r'^\d+$')
#1996
filter_year_in = re.compile(r'^\d{4} in ')
#1996 in the United Kingdom
filter_List_of = re.compile(r'^List of ')
#List of windmills in the United Kingdom
filter_disambiguation_title = re.compile(r'\(disambiguation\)$')

##
# page filtering logic -- remove templates, undesired xml namespaces, and disambiguation pages
def keepPage_lu(ns, title, page):
    if ns != '0':               # Aritcle
        return False
    
    if filter_month_year.match(title):
        return False
    if filter_month_day.match(title):
        return False
    if filter_pure_number.match(title):
        return False
    if filter_year_in.match(title):
        return False
    if filter_List_of.match(title):
        return False    
        
    # remove disambig pages if desired
    if filter_disambig_pages:
        if filter_disambiguation_title.search(title):
            return False
        for line in page:
            if filter_disambig_page_pattern.match(line):
                return False
    return True


# page filtering logic -- remove templates, undesired xml namespaces, and disambiguation pages
def keepPage(ns, page):
    if ns != '0':               # Aritcle
        return False
    # remove disambig pages if desired
    if filter_disambig_pages:
        for line in page:
            if filter_disambig_page_pattern.match(line):
                return False
    return True





def get_url(uid):
    return "%s?curid=%s" % (urlbase, uid)


# =========================================================================
#
# MediaWiki Markup Grammar
# https://www.mediawiki.org/wiki/Preprocessor_ABNF

# xml-char = %x9 / %xA / %xD / %x20-D7FF / %xE000-FFFD / %x10000-10FFFF
# sptab = SP / HTAB

# ; everything except ">" (%x3E)
# attr-char = %x9 / %xA / %xD / %x20-3D / %x3F-D7FF / %xE000-FFFD / %x10000-10FFFF

# literal         = *xml-char
# title           = wikitext-L3
# part-name       = wikitext-L3
# part-value      = wikitext-L3
# part            = ( part-name "=" part-value ) / ( part-value )
# parts           = [ title *( "|" part ) ]
# tplarg          = "{{{" parts "}}}"
# template        = "{{" parts "}}"
# link            = "[[" wikitext-L3 "]]"

# comment         = "<!--" literal "-->"
# unclosed-comment = "<!--" literal END
# ; the + in the line-eating-comment rule was absent between MW 1.12 and MW 1.22
# line-eating-comment = LF LINE-START *SP +( comment *SP ) LINE-END

# attr            = *attr-char
# nowiki-element  = "<nowiki" attr ( "/>" / ( ">" literal ( "</nowiki>" / END ) ) )

# wikitext-L2     = heading / wikitext-L3 / *wikitext-L2
# wikitext-L3     = literal / template / tplarg / link / comment /
#                   line-eating-comment / unclosed-comment / xmlish-element /
#                   *wikitext-L3

# ------------------------------------------------------------------------------

selfClosingTags = ('br', 'hr', 'nobr', 'ref', 'references', 'nowiki')

# These tags are dropped, keeping their content.
# handle 'a' separately, depending on keepLinks
ignoredTags = (
    'abbr', 'b', 'big', 'blockquote', 'center', 'cite', 'em',
    'font', 'h1', 'h2', 'h3', 'h4', 'hiero', 'i', 'kbd',
    'p', 'plaintext', 's', 'span', 'strike', 'strong',
    'tt', 'u', 'var'
)

placeholder_tags = {'math': 'formula', 'code': 'codice'}


def normalizeTitle(title):
    """Normalize title"""
    # remove leading/trailing whitespace and underscores
    title = title.strip(' _')
    # replace sequences of whitespace and underscore chars with a single space
    title = re.sub(r'[\s_]+', ' ', title)

    m = re.match(r'([^:]*):(\s*)(\S(?:.*))', title)
    if m:
        prefix = m.group(1)
        if m.group(2):
            optionalWhitespace = ' '
        else:
            optionalWhitespace = ''
        rest = m.group(3)

        ns = normalizeNamespace(prefix)
        if ns in knownNamespaces:
            # If the prefix designates a known namespace, then it might be
            # followed by optional whitespace that should be removed to get
            # the canonical page name
            # (e.g., "Category:  Births" should become "Category:Births").
            title = ns + ":" + ucfirst(rest)
        else:
            # No namespace, just capitalize first letter.
            # If the part before the colon is not a known namespace, then we
            # must not remove the space after the colon (if any), e.g.,
            # "3001: The_Final_Odyssey" != "3001:The_Final_Odyssey".
            # However, to get the canonical page name we must contract multiple
            # spaces into one, because
            # "3001:   The_Final_Odyssey" != "3001: The_Final_Odyssey".
            title = ucfirst(prefix) + ":" + optionalWhitespace + ucfirst(rest)
    else:
        # no namespace, just capitalize first letter
        title = ucfirst(title)
    return title


def unescape(text):
    """
    Removes HTML or XML character references and entities from a text string.

    :param text The HTML (or XML) source text.
    :return The plain text, as a Unicode string, if necessary.
    """

    def fixup(m):
        text = m.group(0)
        code = m.group(1)
        try:
            if text[1] == "#":  # character reference
                if text[2] == "x":
                    return chr(int(code[1:], 16))
                else:
                    return chr(int(code))
            else:  # named entity
                return chr(name2codepoint[code])
        except:
            return text  # leave as is

    return re.sub("&#?(\w+);", fixup, text)


# Match HTML comments
# The buggy template {{Template:T}} has a comment terminating with just "->"
comment = re.compile(r'<!--.*?-->', re.DOTALL)


# Match <nowiki>...</nowiki>
nowiki = re.compile(r'<nowiki>.*?</nowiki>')


# Match ignored tags
ignored_tag_patterns = []


def ignoreTag(tag):
    left = re.compile(r'<%s\b.*?>' % tag, re.IGNORECASE | re.DOTALL)  # both <ref> and <reference>
    right = re.compile(r'</\s*%s>' % tag, re.IGNORECASE)
    ignored_tag_patterns.append((left, right))


for tag in ignoredTags:
    ignoreTag(tag)

# Match selfClosing HTML tags
selfClosing_tag_patterns = [
    re.compile(r'<\s*%s\b[^>]*/\s*>' % tag, re.DOTALL | re.IGNORECASE) for tag in selfClosingTags
    ]

# Match HTML placeholder tags
placeholder_tag_patterns = [
    (re.compile(r'<\s*%s(\s*| [^>]+?)>.*?<\s*/\s*%s\s*>' % (tag, tag), re.DOTALL | re.IGNORECASE),
     repl) for tag, repl in placeholder_tags.items()
    ]

# Match preformatted lines
preformatted = re.compile(r'^ .*?$')

# Match external links (space separates second optional parameter)
externalLink = re.compile(r'\[\w+[^ ]*? (.*?)]')
externalLinkNoAnchor = re.compile(r'\[\w+[&\]]*\]')

# Matches bold/italic
bold_italic = re.compile(r"'''''(.*?)'''''")
bold = re.compile(r"'''(.*?)'''")
italic_quote = re.compile(r"''\"([^\"]*?)\"''")
italic = re.compile(r"''(.*?)''")
quote_quote = re.compile(r'""([^"]*?)""')

# Matches space
spaces = re.compile(r' {2,}')

# Matches dots
dots = re.compile(r'\.{4,}')

#this reTag match with 5 kinds of marks
#REmainarticleetcmark_lu = re.compile(r'\{\{(Related articles)\|(.*?)\}\}|\{\{(Main article)\|(.*?)\}\}|\{\{(See also)\|(.*?)\}\}|\{\{(Further information)\|(.*?)\}\}|\{\{(Main)\|(.*?)\}\}', re.IGNORECASE)
REmainarticleetcmark_lu = re.compile(r'\{\{(Related articles)\|(.*?)\}\}|\{\{(Main article)\|(.*?)\}\}|\{\{(See also)\|(.*?)\}\}|\{\{(Further information)\|(.*?)\}\}|\{\{(Main)\|(.*?)\}\}|\{\{(details\|topic=(?:[^|]+))\|(.*?)\}\}|\{\{(Further)\|(.*?)\}\}', re.IGNORECASE)
#lu: {{Related articles|Anarchist terminology}},
#lu: {{Main article|Anarcho-syndicalism|International Workers' Association|Anarchism in Spain|Spanish Revolution}}
#lu: {{See also|Anarchism in France|Anarchism in Italy|Anarchism in Spain|Anarchism in Germany}}
#lu: {{Further information|Dynasties in Chinese history}}
#lu: {{Main|自然地理学}}
#lu: {{details|topic=the digital rights management restrictions|iOS (Apple)#Digital rights management}}
REmainarticleetcmark_lu2 = re.compile(r'\[\[\d+=([^\]]+?)\]\]')
#lu: {{Main article|1=Björn Ulvaeus|2=Benny Andersson}}  [[1=Björn Ulvaeus]] [[2=Benny Andersson]]


REquotemark1_lu = re.compile(r'\{\{quote ?\|([^{]+)\}\}',re.IGNORECASE)
#lu: {{quote|This morning, as for some days past, it seems exceedingly probable that this Administration will not be re-elected. Then it will be my duty to so co-operate with the President elect, as to save the Union between the election and the inauguration; as he will have secured his election on such ground that he cannot possibly save it afterward.&lt;ref&gt;Basler (1953), p. 514.&lt;/ref&gt;}}
#REquotemark2_lu = re.compile(r'\{\{quote box ?\|(?:[^}]+)quote=(.+)\}\}',re.IGNORECASE)
REquotemark2_lu = re.compile(r'\{\{quote box ?\|(?:[^}]+)quote=(.+?)(?:\|source=(.+))\}\}',re.IGNORECASE)
#lu: {{quote box |width=30em | bgcolor=#c6dbf7 |align=right |qalign=justify | fontsize=10px | title=The [[Judicial system of Finland#Courts of Appeal|Court of Appeal]] did not change the sentence of the Huopalahdentie road killer| quote=&quot;The Court of Appeal did not change the sentence of the man who ran over a girl by a car on Huopalahdentie road. The Helsinki Court of Appeal did not alter the 18 months prison sentence without chance of parole adjudged by the [[Judicial system of Finland#District Courts|district court]] more than a year ago. The fatal accident took place on Huopalahdentie on August 2002, when a man in his thirties disregarded the instructions of a red traffic light. The girl run over on a pedestrian crossing was killed. The parents of the girl demanded to raise the sentence to two years. The man who drove the car demanded to [[Commutation of sentence|commute]] the verdict issued by the district court. The man denied explicitly running a red light but the Court of Appeal stated that it was substantiated that the lights had been red at least five seconds at the moment the man crossed the pedestrian crossing. There was a 50 km/h speed limit at the site of the incident. The man agreed in the Court of Appeal that the speed of the vehicle he was driving was so high that he would not have been able to stop the car before the junction.&quot; |source= — Helsingin Sanomat, 21 May 2004. Translated from Finnish language.{{sfn|murha.info|2008}}}}   
#lu: {{Quote box|width=25em|align=left|bgcolor=#ACE1AF|quote="Revolution is not a dinner party, nor an essay, nor a painting, nor a piece of embroidery; it cannot be so refined, so leisurely and gentle, so temperate, kind, courteous, restrained and magnanimous. A revolution is an insurrection, an act of violence by which one class overthrows another."|source=— Mao, February 1927.<ref>{{cite web|url= http://afe.easia.columbia.edu/special/china_1900_mao_war.htm |title= Mao Zedong on War and Revolution |publisher= Columbia University |work= Quotations from Mao Zedong on War and Revolution |accessdate= November 12, 2011 }}; {{harvnb|Feigon|2002|p=41}}</ref> }}
REyearmonthmark_lu = re.compile(r'\{\{As of ?\|(\d+)\|(\d+)\}\}',re.IGNORECASE)
#{{As of|2014|10}}
REdistancemark_lu = re.compile(r'\{\{convert ?\|(\d+)\|(\w+)\|abbr=on\}\}',re.IGNORECASE)
#{{convert|160|km|abbr=on}}
REformatnummark_lu = re.compile(r'\{\{formatnum ?\:(\d+)\}\}',re.IGNORECASE)
#{{formatnum:300000}}
REspacedndash_lu = re.compile(r'(\{\{spaced ndash\}\})',re.IGNORECASE)
#{{spaced ndash}}
REnsbp_lu = re.compile(r'&nbsp;',re.IGNORECASE)
#at 12:33&nbsp;am 
# ======================================================================


class Template(list):
    """
    A Template is a list of TemplateText or TemplateArgs
    """

    @classmethod
    def parse(cls, body):
        tpl = Template()
        # we must handle nesting, s.a.
        # {{{1|{{PAGENAME}}}
        # {{{italics|{{{italic|}}}
        # {{#if:{{{{{#if:{{{nominee|}}}|nominee|candidate}}|}}}|
        #
        start = 0
        for s, e in findMatchingBraces(body, 3):
            tpl.append(TemplateText(body[start:s]))
            tpl.append(TemplateArg(body[s + 3:e - 3]))
            start = e
        tpl.append(TemplateText(body[start:]))  # leftover
        return tpl

    def subst(self, params, extractor, depth=0):
        # We perform parameter substitutions recursively.
        # We also limit the maximum number of iterations to avoid too long or
        # even endless loops (in case of malformed input).

        # :see: http://meta.wikimedia.org/wiki/Help:Expansion#Distinction_between_variables.2C_parser_functions.2C_and_templates
        #
        # Parameter values are assigned to parameters in two (?) passes.
        # Therefore a parameter name in a template can depend on the value of
        # another parameter of the same template, regardless of the order in
        # which they are specified in the template call, for example, using
        # Template:ppp containing "{{{{{{p}}}}}}", {{ppp|p=q|q=r}} and even
        # {{ppp|q=r|p=q}} gives r, but using Template:tvvv containing
        # "{{{{{{{{{p}}}}}}}}}", {{tvvv|p=q|q=r|r=s}} gives s.

        # logging.debug('&*ssubst tpl %d %s', extractor.frame.length, '', depth, self)

        if depth > extractor.maxParameterRecursionLevels:
            extractor.recursion_exceeded_3_errs += 1
            return ''

        return ''.join([tpl.subst(params, extractor, depth) for tpl in self])

    def __str__(self):
        return ''.join([text_type(x) for x in self])


class TemplateText(text_type):
    """Fixed text of template"""

    def subst(self, params, extractor, depth):
        return self


class TemplateArg(object):
    """
    parameter to a template.
    Has a name and a default value, both of which are Templates.
    """

    def __init__(self, parameter):
        """
        :param parameter: the parts of a tplarg.
        """
        # the parameter name itself might contain templates, e.g.:
        #   appointe{{#if:{{{appointer14|}}}|r|d}}14|
        #   4|{{{{{subst|}}}CURRENTYEAR}}

        # any parts in a tplarg after the first (the parameter default) are
        # ignored, and an equals sign in the first part is treated as plain text.
        # logging.debug('TemplateArg %s', parameter)

        parts = splitParts(parameter)
        self.name = Template.parse(parts[0])
        if len(parts) > 1:
            # This parameter has a default value
            self.default = Template.parse(parts[1])
        else:
            self.default = None

    def __str__(self):
        if self.default:
            return '{{{%s|%s}}}' % (self.name, self.default)
        else:
            return '{{{%s}}}' % self.name

    def subst(self, params, extractor, depth):
        """
        Substitute value for this argument from dict :param params:
        Use :param extractor: to evaluate expressions for name and default.
        Limit substitution to the maximun :param depth:.
        """
        # the parameter name itself might contain templates, e.g.:
        # appointe{{#if:{{{appointer14|}}}|r|d}}14|
        paramName = self.name.subst(params, extractor, depth + 1)
        paramName = extractor.transform(paramName)
        res = ''
        if paramName in params:
            res = params[paramName]  # use parameter value specified in template invocation
        elif self.default:  # use the default value
            defaultValue = self.default.subst(params, extractor, depth + 1)
            res = extractor.transform(defaultValue)
        # logging.debug('subst arg %d %s -> %s' % (depth, paramName, res))
        return res


class Frame(object):

    def __init__(self, title='', args=[], prev=None):
        self.title = title
        self.args = args
        self.prev = prev
        self.depth = prev.depth + 1 if prev else 0

    def push(self, title, args):
        return Frame(title, args, self)

    def pop(self):
        return self.prev

    def __str__(self):
        res = ''
        prev = this.prev
        while prev:
            if res: res += ', '
            res += '(%s, %s)' % (prev.title, prev.args)
            prev = prev.prev
        return '<Frame [' + res + ']>'

# ======================================================================

substWords = 'subst:|safesubst:'

class Extractor(object):
    """
    An extraction task on a article.
    """
    ##
    # Whether to preserve links in output
    keepLinks = False

    ##
    # Whether to preserve section titles
    keepSections = True

    ##
    # Whether to preserve lists
    keepLists = False

    ##
    # Whether to output HTML instead of text
    toHTML = False

    ##
    # Whether to expand templates
    expand_templates = True

    ##
    ## Whether to escape doc content
    escape_doc = False

    ##
    # Print the wikipedia article revision
    print_revision = False

    ##
    # Minimum expanded text length required to print document
    min_text_length = 0
    
    ## modified by Lu
    # Whether to record lu's information, that is, all of information in '--html', and record other info
    LUstyle = False
    english_stopwords = []

    def __init__(self, id, revid, title, lines):
        """
        :param id: id of page.
        :param title: tutle of page.
        :param lines: a list of lines.
        """
        self.id = id
        self.revid = revid
        self.title = title
        self.text = ''.join(lines)
        self.magicWords = MagicWords()
        self.frame = Frame()
        self.recursion_exceeded_1_errs = 0  # template recursion within expand()
        self.recursion_exceeded_2_errs = 0  # template recursion within expandTemplate()
        self.recursion_exceeded_3_errs = 0  # parameter recursion
        self.template_title_errs = 0


    def extract(self, out):
        """
        :param out: a memory file.
        """
        logging.info('%s\t%s', self.id, self.title)
        url = get_url(self.id)# u'https://en.wikipedia.org/wiki?curid=36785702'
        if Extractor.print_revision:
            header = '<doc id="%s" revid="%s" url="%s" title="%s">\n' % (self.id, self.revid, url, self.title)
        else:
            header = '<doc id="%s" url="%s" title="%s">\n' % (self.id, url, self.title)
        # Separate header from text with a newline.
        if self.toHTML:
            header += '<h1>' + self.title + '</h1>\n'
        else:
            header += self.title + '\n\n'
        # https://www.mediawiki.org/wiki/Help:Magic_words
        self.magicWords['PAGENAME'] = self.title
        self.magicWords['FULLPAGENAME'] = self.title
        self.magicWords['CURRENTYEAR'] = time.strftime('%Y')
        self.magicWords['CURRENTMONTH'] = time.strftime('%m')
        self.magicWords['CURRENTDAY'] = time.strftime('%d')
        self.magicWords['CURRENTHOUR'] = time.strftime('%H')
        self.magicWords['CURRENTTIME'] = time.strftime('%H:%M:%S')
        text = self.text
        self.text = ''          # save memory
        #
        # @see https://doc.wikimedia.org/mediawiki-core/master/php/classParser.html
        # This does the equivalent of internalParse():
        #
        # $dom = $this->preprocessToDom( $text, $flag );
        # $text = $frame->expand( $dom );
        
        #-------------------------------------------
        if self.LUstyle: #lu: this is added by lu
                text = self.changemainarticlemark_lu(text)# call the function designed by Lu, to reserve the mark of main artilce, et al.
                text = self.changeQuotemarkmark_lu(text)
                text = self.changeothermark_lu(text)
        #-------------------------------------------
        #print 'after self.changemainarticlemark_lu(text):'
        #print text #lu
        text = self.transform(text)#lu: transform() function has been modified for LUstyle
        #print 'after self.transform(text):'
        #print text #lu
        text = self.wiki2text(text) #lu: wiki2text() function has been modified for LUstyle
        #print 'after self.wiki2text(text):'
        #print text #lu
        if self.LUstyle == False:
            text = compact(self.clean(text))  #lu: clean() function has been modified for LUstyle
        else:
            text = REnsbp_lu.sub(r' ',text)# avoid a bug for &nbsp;
            text = compact_lustyle(self.clean(text))
            
        #print 'after compact(self.clean(text)):'
        #print text #lu
        
        
        
        footer = "\n</doc>\n"

        if self.LUstyle == False : #lu: this is original code
            if sum(len(line) for line in text) < Extractor.min_text_length:
                return
        if self.LUstyle: #lu: this is added by lu
            #filter out the stopwords and category lines
            text_filtered_stopwords = [[word for word in line.split() if not word.lower() \
            in self.english_stopwords] for line in text if not RECategory1.match(line)]
            #count the number of non-stop words
            if sum(len(line) for line in text_filtered_stopwords) < Extractor.min_text_length:    
                text_filtered_stopwords = None #free memory
                return
            text_filtered_stopwords = None #free memory
            
            
            
        if out == sys.stdout:   # option -a or -o -
            header = header.encode('utf-8')
        out.write(header)
        for line in text:
            if out == sys.stdout:   # option -a or -o -
                line = line.encode('utf-8')
            out.write(line)
            out.write('\n')
        out.write(footer)
        errs = (self.template_title_errs,
                self.recursion_exceeded_1_errs,
                self.recursion_exceeded_2_errs,
                self.recursion_exceeded_3_errs)
        if any(errs):
            logging.warn("Template errors in article '%s' (%s): title(%d) recursion(%d, %d, %d)",
                         self.title, self.id, *errs)


    def changeothermark_lu(self,text):
        '''
        {{As of|2014|10}}   2014 year 10 month
        #{{convert|160|km|abbr=on}}   160 km
        '''
        text = REyearmonthmark_lu.sub(r'\1 \2',text)
        text = REdistancemark_lu.sub(r'\1 \2',text)
        text = REformatnummark_lu.sub(r'\1',text)
        text = REspacedndash_lu.sub(r' – ',text)
        return text



    def changeQuotemarkmark_lu(self,text):
        '''
        {{quote|This morning, as for some days past, it seems exceedingly probable that this Administration will not be re-elected. Then it will be my duty to so co-operate with the President elect, as to save the Union between the election and the inauguration; as he will have secured his election on such ground that he cannot possibly save it afterward.&lt;ref&gt;Basler (1953), p. 514.&lt;/ref&gt;}}
        {{quote box |width=30em | bgcolor=#c6dbf7 |align=right |qalign=justify | fontsize=10px | title=The [[Judicial system of Finland#Courts of Appeal|Court of Appeal]] did not change the sentence of the Huopalahdentie road killer| quote=&quot;The Court of Appeal did not change the sentence of the man who ran over a girl by a car on Huopalahdentie road. The Helsinki Court of Appeal did not alter the 18 months prison sentence without chance of parole adjudged by the [[Judicial system of Finland#District Courts|district court]] more than a year ago. The fatal accident took place on Huopalahdentie on August 2002, when a man in his thirties disregarded the instructions of a red traffic light. The girl run over on a pedestrian crossing was killed. The parents of the girl demanded to raise the sentence to two years. The man who drove the car demanded to [[Commutation of sentence|commute]] the verdict issued by the district court. The man denied explicitly running a red light but the Court of Appeal stated that it was substantiated that the lights had been red at least five seconds at the moment the man crossed the pedestrian crossing. There was a 50 km/h speed limit at the site of the incident. The man agreed in the Court of Appeal that the speed of the vehicle he was driving was so high that he would not have been able to stop the car before the junction.&quot; |source= — Helsingin Sanomat, 21 May 2004. Translated from Finnish language.{{sfn|murha.info|2008}}}}   
        '''
        text = REquotemark1_lu.sub(r'\1',text)
        return REquotemark2_lu.sub(r'\1 \2',text)
        
        

    def changemainarticlemark_lu(self, text):
        """
        if Lustyle is selected, the function is used to change some tags to reserve the information
        lu: this reserves the information such as:
        lu: {{Related articles|Anarchist terminology}},
        lu: {{Main article|History of anarchism}}
        lu: {{Main article|Anarcho-syndicalism|International Workers' Association|Anarchism in Spain|Spanish Revolution}}
        lu: {{See also|Anarchism in France|Anarchism in Italy|Anarchism in Spain|Anarchism in Germany}}
        lu: {{Further information|Dynasties in Chinese history}}
        lu: {{Main article|Politics of China}}{{See also|List of current Chinese provincial leaders}}
        lu: {{Main|自然地理学}}
        lu: I replace them with a link, such as:
        lu: [[Anarchist terminology]]
        lu: {{further|Pronunciation of English ?a?}}
        {{Main article|1=Björn Ulvaeus|2=Benny Andersson}}
        [[Anarcho-syndicalism]][[International Workers' Association]][[Anarchism in Spain|Spanish Revolution]]
        
        
        
        test text:
        text="aaaaa{{Related articles|Anarcho-syndicalism|International Workers' Association|Anarchism in Spain|Spanish Revolution}}\
    bbbbb{{Related articles|Anarchist terminology}}\
    ccccc{{Main article|History of anarchism}}\
    ddddd{{See also|Anarchism in France|Anarchism in Italy|Anarchism in Spain|Anarchism in Germany}}\
    eeeee{{Further information|Dynasties in Chinese history}}\
    fffff{{Main|自然地理学}}ggggg"
        """
           
        start=0
        ret = ''
        
        #print text
        start = 0
        #for m in re.finditer(reTag, text):
        for m in REmainarticleetcmark_lu.finditer(text):
            #print '%02d-%02d: %s' % (m.start(), m.end(), m.group(0))    
            #print m.groups()#('Related articles', "Anarcho-syndicalism|International Workers' Association|Anarchism in Spain|Spanish Revolution")
            #print m.group(0)#{{Related articles|Anarcho-syndicalism|International Workers' Association|Anarchism in Spain|Spanish Revolution}}
            #print m.group(1)#Related articles
            #print m.group(2)#Anarcho-syndicalism|International Workers' Association|Anarchism in Spain|Spanish Revolution
            (s0, e0) = m.span(0)
            ret = ret + text[start:s0]#reserve the left text
            
            a = m.group(m.lastindex)# get the context
            a = '[['+a  # add link mark
            a = a + ']]' # add link mark
            a = re.sub(r'\|',']] [[',a) # replace | with ']] [['            
            a = REmainarticleetcmark_lu2.sub(r'[[\1]]',a)# replace the number in [[1=Björn Ulvaeus]] [[2=Benny Andersson]]
            #print a
            ret = ret + a # reserve the changed text
            #print ret
            start = e0
            
        
        ret = ret + text[start:]#reserve the last text
        #print '\n'
        #print ret    
        return ret
    
        

    def transform(self, wikitext):
        """
        Transforms wiki markup.
        @see https://www.mediawiki.org/wiki/Help:Formatting
        """
        # look for matching <nowiki>...</nowiki>
        res = ''
        cur = 0
        for m in nowiki.finditer(wikitext, cur):#nowiki is a regular expression
            #wikitext[cur:m.start()]#the chars from cur to m.start()
            #wikitext[m.start():m.end()]#the chars in m. from m.start() to m.end()
            #for the chars that don't contain <nowiki>, transform1(); otherwise, keep them unchanged.
            res += self.transform1(wikitext[cur:m.start()]) + wikitext[m.start():m.end()]
            cur = m.end()
        # leftover
        res += self.transform1(wikitext[cur:])
        return res

        
    def transform1(self, text):
        """Transform text not containing <nowiki>"""
        if Extractor.expand_templates:
            # expand templates
            # See: http://www.mediawiki.org/wiki/Help:Templates
            return self.expand(text)
        else:
            # Drop transclusions (template, parser functions)
            return dropNested(text, r'{{', r'}}') 
            

    def wiki2text(self, text):
        #
        # final part of internalParse().)
        #
        # $text = $this->doTableStuff( $text );
        # $text = preg_replace( '/(^|\n)-----*/', '\\1<hr />', $text );
        # $text = $this->doDoubleUnderscore( $text );
        # $text = $this->doHeadings( $text );
        # $text = $this->replaceInternalLinks( $text );
        # $text = $this->doAllQuotes( $text );
        # $text = $this->replaceExternalLinks( $text );
        # $text = str_replace( self::MARKER_PREFIX . 'NOPARSE', '', $text );
        # $text = $this->doMagicLinks( $text );
        # $text = $this->formatHeadings( $text, $origText, $isMain );

        # Drop tables
        # first drop residual templates, or else empty parameter |} might look like end of table.
        text = dropNested(text, r'{{', r'}}')#lu this seems useless, because self.transform(text) has the same process.
        text = dropNested(text, r'{\|', r'\|}')#lu {|  |} is corresponding with the Table in wiki

        # Handle bold/italic/quote
        if self.LUstyle == False:
            #-----------this block is the original code of author-----------
            if self.toHTML:
                text = bold_italic.sub(r'<b>\1</b>', text)#lu replace ''''' mark with <b>
                text = bold.sub(r'<b>\1</b>', text)#lu replace ''' mrak with <b>
                text = italic.sub(r'<i>\1</i>', text)#lu replace '' mark with <i>
            else:
                text = bold_italic.sub(r'\1', text)#lu this means del '''''
                text = bold.sub(r'\1', text)#lu this means del '''
                text = italic_quote.sub(r'"\1"', text)#lu this means to replace ''\" with "
                text = italic.sub(r'"\1"', text)#lu this means to replace '' with "
                text = quote_quote.sub(r'"\1"', text)#lu this means to replace "" with "
        else:
            #----------this block is added by lu, for his style output
            #For Lustyple, the bold, italic, quote is useless.
            #So, I decided to delete them.
            text = bold_italic.sub(r'\1', text)#lu this means del '''''
            text = bold.sub(r'\1', text)#lu this means del '''
            text = italic_quote.sub(r'"\1"', text)#lu this means to replace ''\" with "
            text = italic.sub(r'\1', text)#lu this means del '' 
            text = quote_quote.sub(r'"\1"', text)#lu this means to replace "" with "
        
        
        # residuals of unbalanced quotes 
        text = text.replace("'''", '').replace("''", '"')

        # replace internal links
        if self.LUstyle == False:
            text = replaceInternalLinks(text)  # this is the orginal code of author
        else:
            text = replaceInternalLinks_lustyle(text)  #this is added by lu

        # replace external links
        if self.LUstyle == False:
            text = replaceExternalLinks(text) # this is the original code of author
        else:
            text = replaceExternalLinks_lustyle(text) # this is added by lu

        # drop MagicWords behavioral switches
        text = magicWordsRE.sub('', text)

        # ############### Process HTML ###############

        # turn into HTML, except for the content of <syntaxhighlight>
        res = ''
        cur = 0
        for m in syntaxhighlight.finditer(text):
            res += unescape(text[cur:m.start()]) + m.group(1)
            cur = m.end()
        text = res + unescape(text[cur:])

        return text


    def clean(self, text):
        """
        Removes irrelevant parts from :param: text.
        """

        # Collect spans

        spans = []
        # Drop HTML comments
        for m in comment.finditer(text):
            spans.append((m.start(), m.end()))

        # Drop self-closing tags
        for pattern in selfClosing_tag_patterns:
            for m in pattern.finditer(text):
                spans.append((m.start(), m.end()))

        # Drop ignored tags
        for left, right in ignored_tag_patterns:
            for m in left.finditer(text):
                spans.append((m.start(), m.end()))
            for m in right.finditer(text):
                spans.append((m.start(), m.end()))

        # Bulk remove all spans
        text = dropSpans(spans, text)

        # Drop discarded elements
        for tag in discardElements:
            text = dropNested(text, r'<\s*%s\b[^>/]*>' % tag, r'<\s*/\s*%s>' % tag)

        if not self.toHTML:
            # Turn into text what is left (&amp;nbsp;) and <syntaxhighlight>
            text = unescape(text)

        # Expand placeholders
        for pattern, placeholder in placeholder_tag_patterns:
            index = 1
            for match in pattern.finditer(text):
                text = text.replace(match.group(), '%s_%d' % (placeholder, index))
                index += 1

        text = text.replace('<<', '«').replace('>>', '»')

        #############################################

        # Cleanup text
        text = text.replace('\t', ' ')
        text = spaces.sub(' ', text)
        text = dots.sub('...', text)
        text = re.sub(' (,:\.\)\]»)', r'\1', text)
        text = re.sub('(\[\(«) ', r'\1', text)
        text = re.sub(r'\n\W+?\n', '\n', text, flags=re.U)  # lines with only punctuations
        text = text.replace(',,', ',').replace(',.', '.')
        if self.LUstyle == False:
            if Extractor.toHTML:#lu this block is the original code of author
                text = cgi.escape(text)
        else:
            pass# for LUstyple, don't make:  <ref name="definition">  to  &lt;ref name="definition"&gt; 
        return text


    # ----------------------------------------------------------------------
    # Expand templates

    maxTemplateRecursionLevels = 30
    maxParameterRecursionLevels = 10

    # check for template beginning
    reOpen = re.compile('(?<!{){{(?!{)', re.DOTALL)

    def expand(self, wikitext):
        """
        :param wikitext: the text to be expanded.

        Templates are frequently nested. Occasionally, parsing mistakes may
        cause template insertion to enter an infinite loop, for instance when
        trying to instantiate Template:Country

        {{country_{{{1}}}|{{{2}}}|{{{2}}}|size={{{size|}}}|name={{{name|}}}}}

        which is repeatedly trying to insert template 'country_', which is
        again resolved to Template:Country. The straightforward solution of
        keeping track of templates that were already inserted for the current
        article would not work, because the same template may legally be used
        more than once, with different parameters in different parts of the
        article.  Therefore, we limit the number of iterations of nested
        template inclusion.

        """
        # Test template expansion at:
        # https://en.wikipedia.org/wiki/Special:ExpandTemplates
        # https://it.wikipedia.org/wiki/Speciale:EspandiTemplate

        res = ''
        if self.frame.depth >= self.maxTemplateRecursionLevels:
            self.recursion_exceeded_1_errs += 1
            return res

        # logging.debug('%*s<expand', self.frame.depth, '')

        cur = 0
        # look for matching {{...}}
        for s, e in findMatchingBraces(wikitext, 2):
            res += wikitext[cur:s] + self.expandTemplate(wikitext[s + 2:e - 2])
            cur = e
        # leftover
        res += wikitext[cur:]
        # logging.debug('%*sexpand> %s', self.frame.depth, '', res)
        return res

    def templateParams(self, parameters):
        """
        Build a dictionary with positional or name key to expanded parameters.
        :param parameters: the parts[1:] of a template, i.e. all except the title.
        """
        templateParams = {}

        if not parameters:
            return templateParams
        # logging.debug('%*s<templateParams: %s', self.frame.length, '', '|'.join(parameters))

        # Parameters can be either named or unnamed. In the latter case, their
        # name is defined by their ordinal position (1, 2, 3, ...).

        unnamedParameterCounter = 0

        # It's legal for unnamed parameters to be skipped, in which case they
        # will get default values (if available) during actual instantiation.
        # That is {{template_name|a||c}} means parameter 1 gets
        # the value 'a', parameter 2 value is not defined, and parameter 3 gets
        # the value 'c'.  This case is correctly handled by function 'split',
        # and does not require any special handling.
        for param in parameters:
            # Spaces before or after a parameter value are normally ignored,
            # UNLESS the parameter contains a link (to prevent possible gluing
            # the link to the following text after template substitution)

            # Parameter values may contain "=" symbols, hence the parameter
            # name extends up to the first such symbol.

            # It is legal for a parameter to be specified several times, in
            # which case the last assignment takes precedence. Example:
            # "{{t|a|b|c|2=B}}" is equivalent to "{{t|a|B|c}}".
            # Therefore, we don't check if the parameter has been assigned a
            # value before, because anyway the last assignment should override
            # any previous ones.
            # FIXME: Don't use DOTALL here since parameters may be tags with
            # attributes, e.g. <div class="templatequotecite">
            # Parameters may span several lines, like:
            # {{Reflist|colwidth=30em|refs=
            # &lt;ref name=&quot;Goode&quot;&gt;Title&lt;/ref&gt;

            # The '=' might occurr within an HTML attribute:
            #   "&lt;ref name=value"
            # but we stop at first.
            m = re.match(' *([^=]*?) *?=(.*)', param, re.DOTALL)
            if m:
                # This is a named parameter.  This case also handles parameter
                # assignments like "2=xxx", where the number of an unnamed
                # parameter ("2") is specified explicitly - this is handled
                # transparently.

                parameterName = m.group(1).strip()
                parameterValue = m.group(2)

                if ']]' not in parameterValue:  # if the value does not contain a link, trim whitespace
                    parameterValue = parameterValue.strip()
                templateParams[parameterName] = parameterValue
            else:
                # this is an unnamed parameter
                unnamedParameterCounter += 1

                if ']]' not in param:  # if the value does not contain a link, trim whitespace
                    param = param.strip()
                templateParams[str(unnamedParameterCounter)] = param
        # logging.debug('%*stemplateParams> %s', self.frame.length, '', '|'.join(templateParams.values()))
        return templateParams

    def expandTemplate(self, body):
        """Expands template invocation.
        :param body: the parts of a template.

        :see http://meta.wikimedia.org/wiki/Help:Expansion for an explanation
        of the process.

        See in particular: Expansion of names and values
        http://meta.wikimedia.org/wiki/Help:Expansion#Expansion_of_names_and_values

        For most parser functions all names and values are expanded,
        regardless of what is relevant for the result. The branching functions
        (#if, #ifeq, #iferror, #ifexist, #ifexpr, #switch) are exceptions.

        All names in a template call are expanded, and the titles of the
        tplargs in the template body, after which it is determined which
        values must be expanded, and for which tplargs in the template body
        the first part (default) [sic in the original doc page].

        In the case of a tplarg, any parts beyond the first are never
        expanded.  The possible name and the value of the first part is
        expanded if the title does not match a name in the template call.

        :see code for braceSubstitution at
        https://doc.wikimedia.org/mediawiki-core/master/php/html/Parser_8php_source.html#3397:

        """

        # template        = "{{" parts "}}"

        # Templates and tplargs are decomposed in the same way, with pipes as
        # separator, even though eventually any parts in a tplarg after the first
        # (the parameter default) are ignored, and an equals sign in the first
        # part is treated as plain text.
        # Pipes inside inner templates and tplargs, or inside double rectangular
        # brackets within the template or tplargs are not taken into account in
        # this decomposition.
        # The first part is called title, the other parts are simply called parts.

        # If a part has one or more equals signs in it, the first equals sign
        # determines the division into name = value. Equals signs inside inner
        # templates and tplargs, or inside double rectangular brackets within the
        # part are not taken into account in this decomposition. Parts without
        # equals sign are indexed 1, 2, .., given as attribute in the <name> tag.

        if self.frame.depth >= self.maxTemplateRecursionLevels:
            self.recursion_exceeded_2_errs += 1
            # logging.debug('%*sEXPAND> %s', self.frame.depth, '', body)
            return ''

        logging.debug('%*sEXPAND %s', self.frame.depth, '', body)

        parts = splitParts(body)
        # title is the portion before the first |
        title = parts[0].strip()
        title = self.expand(title)

        # SUBST
        # Apply the template tag to parameters without
        # substituting into them, e.g.
        # {{subst:t|a{{{p|q}}}b}} gives the wikitext start-a{{{p|q}}}b-end
        # @see https://www.mediawiki.org/wiki/Manual:Substitution#Partial_substitution
        subst = False
        if re.match(substWords, title, re.IGNORECASE):
            title = re.sub(substWords, '', title, 1, re.IGNORECASE)
            subst = True

        if title in self.magicWords.values:
            ret = self.magicWords[title]
            logging.debug('%*s<EXPAND %s %s', self.frame.depth, '', title, ret)
            return ret

        # Parser functions.

        # For most parser functions all names and values are expanded,
        # regardless of what is relevant for the result. The branching
        # functions (#if, #ifeq, #iferror, #ifexist, #ifexpr, #switch) are
        # exceptions: for #if, #iferror, #ifexist, #ifexp, only the part that
        # is applicable is expanded; for #ifeq the first and the applicable
        # part are expanded; for #switch, expanded are the names up to and
        # including the match (or all if there is no match), and the value in
        # the case of a match or if there is no match, the default, if any.

        # The first argument is everything after the first colon.
        # It has been evaluated above.
        colon = title.find(':')
        if colon > 1:
            funct = title[:colon]
            parts[0] = title[colon + 1:].strip()  # side-effect (parts[0] not used later)
            # arguments after first are not evaluated
            ret = callParserFunction(funct, parts, self)
            logging.debug('%*s<EXPAND %s %s', self.frame.depth, '', funct, ret)
            return ret

        title = fullyQualifiedTemplateTitle(title)
        if not title:
            self.template_title_errs += 1
            return ''

        redirected = redirects.get(title)
        if redirected:
            title = redirected

        # get the template
        if title in templateCache:
            template = templateCache[title]
        elif title in templates:
            template = Template.parse(templates[title])
            # add it to cache
            templateCache[title] = template
            del templates[title]
        else:
            # The page being included could not be identified
            logging.debug('%*s<EXPAND %s %s', self.frame.depth, '', title, '')
            return ''

        logging.debug('%*sTEMPLATE %s: %s', self.frame.depth, '', title, template)

        # tplarg          = "{{{" parts "}}}"
        # parts           = [ title *( "|" part ) ]
        # part            = ( part-name "=" part-value ) / ( part-value )
        # part-name       = wikitext-L3
        # part-value      = wikitext-L3
        # wikitext-L3     = literal / template / tplarg / link / comment /
        #                   line-eating-comment / unclosed-comment /
        #           	    xmlish-element / *wikitext-L3

        # A tplarg may contain other parameters as well as templates, e.g.:
        #   {{{text|{{{quote|{{{1|{{error|Error: No text given}}}}}}}}}}}
        # hence no simple RE like this would work:
        #   '{{{((?:(?!{{{).)*?)}}}'
        # We must use full CF parsing.

        # the parameter name itself might be computed, e.g.:
        #   {{{appointe{{#if:{{{appointer14|}}}|r|d}}14|}}}

        # Because of the multiple uses of double-brace and triple-brace
        # syntax, expressions can sometimes be ambiguous.
        # Precedence rules specifed here:
        # http://www.mediawiki.org/wiki/Preprocessor_ABNF#Ideal_precedence
        # resolve ambiguities like this:
        #   {{{{ }}}} -> { {{{ }}} }
        #   {{{{{ }}}}} -> {{ {{{ }}} }}
        #
        # :see: https://en.wikipedia.org/wiki/Help:Template#Handling_parameters

        params = parts[1:]

        # Order of evaluation.
        # Template parameters are fully evaluated before they are passed to the template.
        # :see: https://www.mediawiki.org/wiki/Help:Templates#Order_of_evaluation
        if not subst:
            # Evaluate parameters, since they may contain templates, including
            # the symbol "=".
            # {{#ifexpr: {{{1}}} = 1 }}
            params = [self.transform(p) for p in params]

        # build a dict of name-values for the parameter values
        params = self.templateParams(params)

        # Perform parameter substitution.
        # Extend frame before subst, since there may be recursion in default
        # parameter value, e.g. {{OTRS|celebrative|date=April 2015}} in article
        # 21637542 in enwiki.
        self.frame = self.frame.push(title, params)
        instantiated = template.subst(params, self)
        value = self.transform(instantiated)
        self.frame = self.frame.pop()
        logging.debug('%*s<EXPAND %s %s', self.frame.depth, '', title, value)
        return value


# ----------------------------------------------------------------------
# parameter handling


def splitParts(paramsList):
    """
    :param paramsList: the parts of a template or tplarg.

    Split template parameters at the separator "|".
    separator "=".

    Template parameters often contain URLs, internal links, text or even
    template expressions, since we evaluate templates outside in.
    This is required for cases like:
      {{#if: {{{1}}} | {{lc:{{{1}}} | "parameter missing"}}
    Parameters are separated by "|" symbols. However, we
    cannot simply split the string on "|" symbols, since these
    also appear inside templates and internal links, e.g.

     {{if:|
      |{{#if:the president|
           |{{#if:|
               [[Category:Hatnote templates|A{{PAGENAME}}]]
            }}
       }}
     }}

    We split parts at the "|" symbols that are not inside any pair
    {{{...}}}, {{...}}, [[...]], {|...|}.
    """

    # Must consider '[' as normal in expansion of Template:EMedicine2:
    # #ifeq: ped|article|[http://emedicine.medscape.com/article/180-overview|[http://www.emedicine.com/ped/topic180.htm#{{#if: |section~}}
    # as part of:
    # {{#ifeq: ped|article|[http://emedicine.medscape.com/article/180-overview|[http://www.emedicine.com/ped/topic180.htm#{{#if: |section~}}}} ped/180{{#if: |~}}]

    # should handle both tpl arg like:
    #    4|{{{{{subst|}}}CURRENTYEAR}}
    # and tpl parameters like:
    #    ||[[Category:People|{{#if:A|A|{{PAGENAME}}}}]]

    sep = '|'
    parameters = []
    cur = 0
    for s, e in findMatchingBraces(paramsList):
        par = paramsList[cur:s].split(sep)
        if par:
            if parameters:
                # portion before | belongs to previous parameter
                parameters[-1] += par[0]
                if len(par) > 1:
                    # rest are new parameters
                    parameters.extend(par[1:])
            else:
                parameters = par
        elif not parameters:
            parameters = ['']  # create first param
        # add span to last previous parameter
        parameters[-1] += paramsList[s:e]
        cur = e
    # leftover
    par = paramsList[cur:].split(sep)
    if par:
        if parameters:
            # portion before | belongs to previous parameter
            parameters[-1] += par[0]
            if len(par) > 1:
                # rest are new parameters
                parameters.extend(par[1:])
        else:
            parameters = par

    # logging.debug('splitParts %s %s\nparams: %s', sep, paramsList, str(parameters))
    return parameters


def findMatchingBraces(text, ldelim=0):
    """
    :param ldelim: number of braces to match. 0 means match [[]], {{}} and {{{}}}.
    """
    # Parsing is done with respect to pairs of double braces {{..}} delimiting
    # a template, and pairs of triple braces {{{..}}} delimiting a tplarg.
    # If double opening braces are followed by triple closing braces or
    # conversely, this is taken as delimiting a template, with one left-over
    # brace outside it, taken as plain text. For any pattern of braces this
    # defines a set of templates and tplargs such that any two are either
    # separate or nested (not overlapping).

    # Unmatched double rectangular closing brackets can be in a template or
    # tplarg, but unmatched double rectangular opening brackets cannot.
    # Unmatched double or triple closing braces inside a pair of
    # double rectangular brackets are treated as plain text.
    # Other formulation: in ambiguity between template or tplarg on one hand,
    # and a link on the other hand, the structure with the rightmost opening
    # takes precedence, even if this is the opening of a link without any
    # closing, so not producing an actual link.

    # In the case of more than three opening braces the last three are assumed
    # to belong to a tplarg, unless there is no matching triple of closing
    # braces, in which case the last two opening braces are are assumed to
    # belong to a template.

    # We must skip individual { like in:
    #   {{#ifeq: {{padleft:|1|}} | { | | &nbsp;}}
    # We must resolve ambiguities like this:
    #   {{{{ }}}} -> { {{{ }}} }
    #   {{{{{ }}}}} -> {{ {{{ }}} }}
    #   {{#if:{{{{{#if:{{{nominee|}}}|nominee|candidate}}|}}}|...}}
    #   {{{!}} {{!}}}

    # Handle:
    #   {{{{{|safesubst:}}}#Invoke:String|replace|{{{1|{{{{{|safesubst:}}}PAGENAME}}}}}|%s+%([^%(]-%)$||plain=false}}
    # as well as expressions with stray }:
    #   {{{link|{{ucfirst:{{{1}}}}}} interchange}}}

    if ldelim:  # 2-3
        reOpen = re.compile('[{]{%d,}' % ldelim)  # at least ldelim
        reNext = re.compile('[{]{2,}|}{2,}')  # at least 2
    else:
        reOpen = re.compile('{{2,}|\[{2,}')
        reNext = re.compile('{{2,}|}{2,}|\[{2,}|]{2,}')  # at least 2

    cur = 0
    while True:
        m1 = reOpen.search(text, cur)
        if not m1:
            return
        lmatch = m1.end() - m1.start()
        if m1.group()[0] == '{':
            stack = [lmatch]  # stack of opening braces lengths
        else:
            stack = [-lmatch]  # negative means [
        end = m1.end()
        while True:
            m2 = reNext.search(text, end)
            if not m2:
                return  # unbalanced
            end = m2.end()
            brac = m2.group()[0]
            lmatch = m2.end() - m2.start()

            if brac == '{':
                stack.append(lmatch)
            elif brac == '}':
                while stack:
                    openCount = stack.pop()  # opening span
                    if openCount == 0:  # illegal unmatched [[
                        continue
                    if lmatch >= openCount:
                        lmatch -= openCount
                        if lmatch <= 1:  # either close or stray }
                            break
                    else:
                        # put back unmatched
                        stack.append(openCount - lmatch)
                        break
                if not stack:
                    yield m1.start(), end - lmatch
                    cur = end
                    break
                elif len(stack) == 1 and 0 < stack[0] < ldelim:
                    # ambiguous {{{{{ }}} }}
                    #yield m1.start() + stack[0], end
                    cur = end
                    break
            elif brac == '[':  # [[
                stack.append(-lmatch)
            else:  # ]]
                while stack and stack[-1] < 0:  # matching [[
                    openCount = -stack.pop()
                    if lmatch >= openCount:
                        lmatch -= openCount
                        if lmatch <= 1:  # either close or stray ]
                            break
                    else:
                        # put back unmatched (negative)
                        stack.append(lmatch - openCount)
                        break
                if not stack:
                    yield m1.start(), end - lmatch
                    cur = end
                    break
                # unmatched ]] are discarded
                cur = end


def findBalanced(text, openDelim=['[['], closeDelim=[']]']):
    """
    Assuming that text contains a properly balanced expression using
    :param openDelim: as opening delimiters and
    :param closeDelim: as closing delimiters.
    :return: an iterator producing pairs (start, end) of start and end
    positions in text containing a balanced expression.
    """
    openPat = '|'.join([re.escape(x) for x in openDelim])
    # pattern for delimiters expected after each opening delimiter
    afterPat = {o: re.compile(openPat + '|' + c, re.DOTALL) for o, c in zip(openDelim, closeDelim)}
    stack = []
    start = 0
    cur = 0
    # end = len(text)
    startSet = False
    startPat = re.compile(openPat)
    nextPat = startPat
    while True:
        next = nextPat.search(text, cur)
        if not next:
            return
        if not startSet:
            start = next.start()
            startSet = True
        delim = next.group(0)
        if delim in openDelim:
            stack.append(delim)
            nextPat = afterPat[delim]
        else:
            opening = stack.pop()
            # assert opening == openDelim[closeDelim.index(next.group(0))]
            if stack:
                nextPat = afterPat[stack[-1]]
            else:
                yield start, next.end()
                nextPat = startPat
                start = next.end()
                startSet = False
        cur = next.end()


# ----------------------------------------------------------------------
# Modules

# Only minimal support
# FIXME: import Lua modules.

def if_empty(*rest):
    """
    This implements If_empty from English Wikipedia module:

       <title>Module:If empty</title>
       <ns>828</ns>
       <text>local p = {}

    function p.main(frame)
            local args = require('Module:Arguments').getArgs(frame, {wrappers = 'Template:If empty', removeBlanks = false})

            -- For backwards compatibility reasons, the first 8 parameters can be unset instead of being blank,
            -- even though there's really no legitimate use case for this. At some point, this will be removed.
            local lowestNil = math.huge
            for i = 8,1,-1 do
                    if args[i] == nil then
                            args[i] = ''
                            lowestNil = i
                    end
            end

            for k,v in ipairs(args) do
                    if v ~= '' then
                            if lowestNil &lt; k then
                                    -- If any uses of this template depend on the behavior above, add them to a tracking category.
                                    -- This is a rather fragile, convoluted, hacky way to do it, but it ensures that this module's output won't be modified
                                    -- by it.
                                    frame:extensionTag('ref', '[[Category:Instances of Template:If_empty missing arguments]]', {group = 'TrackingCategory'})
                                    frame:extensionTag('references', '', {group = 'TrackingCategory'})
                            end
                            return v
                    end
            end
    end

    return p   </text>
    """
    for arg in rest:
        if arg:
            return arg
    return ''


# ----------------------------------------------------------------------
# String module emulation
# https://it.wikipedia.org/wiki/Modulo:String

def functionParams(args, vars):
    """
    Build a dictionary of var/value from :param: args.
    Parameters can be either named or unnamed. In the latter case, their
    name is taken fron :param: vars.
    """
    params = {}
    index = 1
    for var in vars:
        value = args.get(var)
        if value is None:
            value = args.get(str(index))
            if value is None:
                value = ''
            else:
                index += 1
        params[var] = value
    return params

def string_sub(args):
    params = functionParams(args, ('s', 'i', 'j'))
    s = params.get('s', '')
    i = int(params.get('i', 1) or 1) # or handles case of '' value
    j = int(params.get('j', -1) or -1)
    if i > 0: i -= 1             # lua is 1-based
    if j < 0: j += 1
    if j == 0: j = len(s)
    return s[i:j]


def string_len(args):
    params = functionParams(args, ('s'))
    s = params.get('s', '')
    return len(s)

def string_find(args):
    params = functionParams(args, ('source', 'target', 'start', 'plain'))
    source = params.get('source', '')
    pattern = params.get('target', '')
    start = int('0'+params.get('start', 1)) - 1 # lua is 1-based
    plain = int('0'+params.get('plain', 1))
    if source == '' or pattern == '':
        return 0
    if plain:
        return source.find(pattern, start) + 1 # lua is 1-based
    else:
        return (re.compile(pattern).search(source, start) or -1) + 1
        
# ----------------------------------------------------------------------
# Module:Roman
# http://en.wikipedia.org/w/index.php?title=Module:Roman
# Modulo:Numero_romano
# https://it.wikipedia.org/wiki/Modulo:Numero_romano

def roman_main(args):
    """Convert first arg to roman numeral if <= 5000 else :return: second arg."""
    num = int(float(args.get('1')))
 
    # Return a message for numbers too big to be expressed in Roman numerals.
    if 0 > num or num >= 5000:
        return args.get('2', 'N/A')
 
    def toRoman(n, romanNumeralMap):
        """convert integer to Roman numeral"""
        result = ""
        for integer, numeral in romanNumeralMap:
            while n >= integer:
                result += numeral
                n -= integer
        return result

    # Find the Roman numerals for numbers 4999 or less.
    smallRomans = (
        (1000, "M"),
        (900, "CM"), (500, "D"), (400, "CD"), (100, "C"),
        (90, "XC"), (50, "L"), (40, "XL"), (10, "X"),
        (9, "IX"), (5, "V"), (4, "IV"), (1, "I") 
    )
    return toRoman(num, smallRomans)

# ----------------------------------------------------------------------

modules = {
    'convert': {
        'convert': lambda x, u, *rest: x + ' ' + u,  # no conversion
    },

    'If empty': {
        'main': if_empty
    },

    'String': {
        'sub': string_sub,
        'len': string_len,
        'find': string_find
    },

    'Roman': {
        'main': roman_main
    },

    'Numero romano': {
        'main': roman_main
    }
}

# ----------------------------------------------------------------------
# variables


class MagicWords(object):
    """
    One copy in each Extractor.

    @see https://doc.wikimedia.org/mediawiki-core/master/php/MagicWord_8php_source.html
    """
    names = [
        '!',
        'currentmonth',
        'currentmonth1',
        'currentmonthname',
        'currentmonthnamegen',
        'currentmonthabbrev',
        'currentday',
        'currentday2',
        'currentdayname',
        'currentyear',
        'currenttime',
        'currenthour',
        'localmonth',
        'localmonth1',
        'localmonthname',
        'localmonthnamegen',
        'localmonthabbrev',
        'localday',
        'localday2',
        'localdayname',
        'localyear',
        'localtime',
        'localhour',
        'numberofarticles',
        'numberoffiles',
        'numberofedits',
        'articlepath',
        'pageid',
        'sitename',
        'server',
        'servername',
        'scriptpath',
        'stylepath',
        'pagename',
        'pagenamee',
        'fullpagename',
        'fullpagenamee',
        'namespace',
        'namespacee',
        'namespacenumber',
        'currentweek',
        'currentdow',
        'localweek',
        'localdow',
        'revisionid',
        'revisionday',
        'revisionday2',
        'revisionmonth',
        'revisionmonth1',
        'revisionyear',
        'revisiontimestamp',
        'revisionuser',
        'revisionsize',
        'subpagename',
        'subpagenamee',
        'talkspace',
        'talkspacee',
        'subjectspace',
        'subjectspacee',
        'talkpagename',
        'talkpagenamee',
        'subjectpagename',
        'subjectpagenamee',
        'numberofusers',
        'numberofactiveusers',
        'numberofpages',
        'currentversion',
        'rootpagename',
        'rootpagenamee',
        'basepagename',
        'basepagenamee',
        'currenttimestamp',
        'localtimestamp',
        'directionmark',
        'contentlanguage',
        'numberofadmins',
        'cascadingsources',
    ]

    def __init__(self):
        self.values = {'!': '|'}

    def __getitem__(self, name):
        return self.values.get(name)

    def __setitem__(self, name, value):
        self.values[name] = value

    switches = (
        '__NOTOC__',
        '__FORCETOC__',
        '__TOC__',
        '__TOC__',
        '__NEWSECTIONLINK__',
        '__NONEWSECTIONLINK__',
        '__NOGALLERY__',
        '__HIDDENCAT__',
        '__NOCONTENTCONVERT__',
        '__NOCC__',
        '__NOTITLECONVERT__',
        '__NOTC__',
        '__START__',
        '__END__',
        '__INDEX__',
        '__NOINDEX__',
        '__STATICREDIRECT__',
        '__DISAMBIG__'
    )


magicWordsRE = re.compile('|'.join(MagicWords.switches))


# ----------------------------------------------------------------------
# parser functions utilities


def ucfirst(string):
    """:return: a string with just its first character uppercase
    We can't use title() since it coverts all words.
    """
    if string:
        return string[0].upper() + string[1:]
    else:
        return ''


def lcfirst(string):
    """:return: a string with its first character lowercase"""
    if string:
        if len(string) > 1:
            return string[0].lower() + string[1:]
        else:
            return string.lower()
    else:
        return ''


def fullyQualifiedTemplateTitle(templateTitle):
    """
    Determine the namespace of the page being included through the template
    mechanism
    """
    if templateTitle.startswith(':'):
        # Leading colon by itself implies main namespace, so strip this colon
        return ucfirst(templateTitle[1:])
    else:
        m = re.match('([^:]*)(:.*)', templateTitle)
        if m:
            # colon found but not in the first position - check if it
            # designates a known namespace
            prefix = normalizeNamespace(m.group(1))
            if prefix in knownNamespaces:
                return prefix + ucfirst(m.group(2))
    # The title of the page being included is NOT in the main namespace and
    # lacks any other explicit designation of the namespace - therefore, it
    # is resolved to the Template namespace (that's the default for the
    # template inclusion mechanism).

    # This is a defense against pages whose title only contains UTF-8 chars
    # that are reduced to an empty string. Right now I can think of one such
    # case - <C2><A0> which represents the non-breaking space.
    # In this particular case, this page is a redirect to [[Non-nreaking
    # space]], but having in the system a redirect page with an empty title
    # causes numerous problems, so we'll live happier without it.
    if templateTitle:
        return templatePrefix + ucfirst(templateTitle)
    else:
        return ''  # caller may log as error


def normalizeNamespace(ns):
    return ucfirst(ns)


# ----------------------------------------------------------------------
# Parser functions
# see http://www.mediawiki.org/wiki/Help:Extension:ParserFunctions
# https://github.com/Wikia/app/blob/dev/extensions/ParserFunctions/ParserFunctions_body.php


class Infix:
    """Infix operators.
    The calling sequence for the infix is:
      x |op| y
    """

    def __init__(self, function):
        self.function = function

    def __ror__(self, other):
        return Infix(lambda x, self=self, other=other: self.function(other, x))

    def __or__(self, other):
        return self.function(other)

    def __rlshift__(self, other):
        return Infix(lambda x, self=self, other=other: self.function(other, x))

    def __rshift__(self, other):
        return self.function(other)

    def __call__(self, value1, value2):
        return self.function(value1, value2)


ROUND = Infix(lambda x, y: round(x, y))


from math import floor, ceil, pi, e, trunc, exp, log as ln, sin, cos, tan, asin, acos, atan


def sharp_expr(extr, expr):
    """Tries converting a lua expr into a Python expr."""
    try:
        expr = extr.expand(expr)
        expr = re.sub('(?<![!<>])=', '==', expr) # negative lookbehind
        expr = re.sub('mod', '%', expr)          # no \b here
        expr = re.sub('\bdiv\b', '/', expr)
        expr = re.sub('\bround\b', '|ROUND|', expr)
        return text_type(eval(expr))
    except:
        return '<span class="error">%s</span>' % expr


def sharp_if(extr, testValue, valueIfTrue, valueIfFalse=None, *args):
    # In theory, we should evaluate the first argument here,
    # but it was evaluated while evaluating part[0] in expandTemplate().
    if testValue.strip():
        # The {{#if:}} function is an if-then-else construct.
        # The applied condition is: "The condition string is non-empty".
        valueIfTrue = extr.expand(valueIfTrue.strip()) # eval
        if valueIfTrue:
            return valueIfTrue
    elif valueIfFalse:
        return extr.expand(valueIfFalse.strip()) # eval
    return ""


def sharp_ifeq(extr, lvalue, rvalue, valueIfTrue, valueIfFalse=None, *args):
    rvalue = rvalue.strip()
    if rvalue:
        # lvalue is always evaluated
        if lvalue.strip() == rvalue:
            # The {{#ifeq:}} function is an if-then-else construct. The
            # applied condition is "is rvalue equal to lvalue". Note that this
            # does only string comparison while MediaWiki implementation also
            # supports numerical comparissons.

            if valueIfTrue:
                return extr.expand(valueIfTrue.strip())
        else:
            if valueIfFalse:
                return extr.expand(valueIfFalse.strip())
    return ""


def sharp_iferror(extr, test, then='', Else=None, *args):
    if re.match('<(?:strong|span|p|div)\s(?:[^\s>]*\s+)*?class="(?:[^"\s>]*\s+)*?error(?:\s[^">]*)?"', test):
        return extr.expand(then.strip())
    elif Else is None:
        return test.strip()
    else:
        return extr.expand(Else.strip())


def sharp_switch(extr, primary, *params):
    # FIXME: we don't support numeric expressions in primary

    # {{#switch: comparison string
    #  | case1 = result1
    #  | case2
    #  | case4 = result2
    #  | 1 | case5 = result3
    #  | #default = result4
    # }}

    primary = primary.strip()
    found = False  # for fall through cases
    default = None
    rvalue = None
    lvalue = ''
    for param in params:
        # handle cases like:
        #  #default = [http://www.perseus.tufts.edu/hopper/text?doc=Perseus...]
        pair = param.split('=', 1)
        lvalue = extr.expand(pair[0].strip())
        rvalue = None
        if len(pair) > 1:
            # got "="
            rvalue = extr.expand(pair[1].strip())
            # check for any of multiple values pipe separated
            if found or primary in [v.strip() for v in lvalue.split('|')]:
                # Found a match, return now
                return rvalue
            elif lvalue == '#default':
                default = rvalue
            rvalue = None  # avoid defaulting to last case
        elif lvalue == primary:
            # If the value matches, set a flag and continue
            found = True
    # Default case
    # Check if the last item had no = sign, thus specifying the default case
    if rvalue is not None:
        return lvalue
    elif default is not None:
        return default
    return ''


# Extension Scribunto: https://www.mediawiki.org/wiki/Extension:Scribunto
def sharp_invoke(module, function, args):
    functions = modules.get(module)
    if functions:
        funct = functions.get(function)
        if funct:
            return str(funct(args))
    return ''


parserFunctions = {

    '#expr': sharp_expr,

    '#if': sharp_if,

    '#ifeq': sharp_ifeq,

    '#iferror': sharp_iferror,

    '#ifexpr': lambda *args: '',  # not supported

    '#ifexist': lambda *args: '',  # not supported

    '#rel2abs': lambda *args: '',  # not supported

    '#switch': sharp_switch,

    '#language': lambda *args: '',  # not supported

    '#time': lambda *args: '',  # not supported

    '#timel': lambda *args: '',  # not supported

    '#titleparts': lambda *args: '',  # not supported

    # This function is used in some pages to construct links
    # http://meta.wikimedia.org/wiki/Help:URL
    'urlencode': lambda string, *rest: quote(string.encode('utf-8')),

    'lc': lambda string, *rest: string.lower() if string else '',

    'lcfirst': lambda string, *rest: lcfirst(string),

    'uc': lambda string, *rest: string.upper() if string else '',

    'ucfirst': lambda string, *rest: ucfirst(string),

    'int': lambda string, *rest: str(int(string)),

}


def callParserFunction(functionName, args, extractor):
    """
    Parser functions have similar syntax as templates, except that
    the first argument is everything after the first colon.
    :return: the result of the invocation, None in case of failure.

    :param: args not yet expanded (see branching functions).
    https://www.mediawiki.org/wiki/Help:Extension:ParserFunctions
    """

    try:
        # https://it.wikipedia.org/wiki/Template:Str_endswith has #Invoke
        functionName = functionName.lower()
        if functionName == '#invoke':
            module, fun = args[0].strip(), args[1].strip()
            logging.debug('%*s#invoke %s %s %s', extractor.frame.depth, '', module, fun, args[2:])
            # special handling of frame
            if len(args) == 2:
                # find parameters in frame whose title is the one of the original
                # template invocation
                templateTitle = fullyQualifiedTemplateTitle(module)
                if not templateTitle:
                    logging.warn("Template with empty title")
                params = None
                frame = extractor.frame
                while frame:
                    if frame.title == templateTitle:
                        params = frame.args
                        break
                    frame = frame.prev
            else:
                params = [extractor.transform(p) for p in args[2:]] # evaluates them
                params = extractor.templateParams(params)
            ret = sharp_invoke(module, fun, params)
            logging.debug('%*s<#invoke %s %s %s', extractor.frame.depth, '', module, fun, ret)
            return ret
        if functionName in parserFunctions:
            # branching functions use the extractor to selectively evaluate args
            return parserFunctions[functionName](extractor, *args)
    except:
        return ""  # FIXME: fix errors
    return ""


# ----------------------------------------------------------------------
# Expand using WikiMedia API
# import json

# def expand(text):
#     """Expand templates invoking MediaWiki API"""
#     text = urlib.urlencodew(text.encode('utf-8'))
#     base = urlbase[:urlbase.rfind('/')]
#     url = base + "/w/api.php?action=expandtemplates&format=json&text=" + text
#     exp = json.loads(urllib.urlopen(url))
#     return exp['expandtemplates']['*']

# ----------------------------------------------------------------------
# Extract Template definition

reNoinclude = re.compile(r'<noinclude>(?:.*?)</noinclude>', re.DOTALL)
reIncludeonly = re.compile(r'<includeonly>|</includeonly>', re.DOTALL)

# These are built before spawning processes, hence thay are shared.
templates = {}
redirects = {}
# cache of parser templates
# FIXME: sharing this with a Manager slows down.
templateCache = {}


def define_template(title, page):
    """
    Adds a template defined in the :param page:.
    @see https://en.wikipedia.org/wiki/Help:Template#Noinclude.2C_includeonly.2C_and_onlyinclude
    """
    global templates
    global redirects

    # title = normalizeTitle(title)

    # check for redirects
    m = re.match('#REDIRECT.*?\[\[([^\]]*)]]', page[0], re.IGNORECASE)
    if m:
        redirects[title] = m.group(1)  # normalizeTitle(m.group(1))
        return

    text = unescape(''.join(page))

    # We're storing template text for future inclusion, therefore,
    # remove all <noinclude> text and keep all <includeonly> text
    # (but eliminate <includeonly> tags per se).
    # However, if <onlyinclude> ... </onlyinclude> parts are present,
    # then only keep them and discard the rest of the template body.
    # This is because using <onlyinclude> on a text fragment is
    # equivalent to enclosing it in <includeonly> tags **AND**
    # enclosing all the rest of the template body in <noinclude> tags.

    # remove comments
    text = comment.sub('', text)

    # eliminate <noinclude> fragments
    text = reNoinclude.sub('', text)
    # eliminate unterminated <noinclude> elements
    text = re.sub(r'<noinclude\s*>.*$', '', text, flags=re.DOTALL)
    text = re.sub(r'<noinclude/>', '', text)

    onlyincludeAccumulator = ''
    for m in re.finditer('<onlyinclude>(.*?)</onlyinclude>', text, re.DOTALL):
        onlyincludeAccumulator += m.group(1)
    if onlyincludeAccumulator:
        text = onlyincludeAccumulator
    else:
        text = reIncludeonly.sub('', text)

    if text:
        if title in templates:
            logging.warn('Redefining: %s', title)
        templates[title] = text


# ----------------------------------------------------------------------

def dropNested(text, openDelim, closeDelim):
    """
    A matching function for nested expressions, e.g. namespaces and tables.
    """
    openRE = re.compile(openDelim, re.IGNORECASE)
    closeRE = re.compile(closeDelim, re.IGNORECASE)
    # partition text in separate blocks { } { }
    spans = []                  # pairs (s, e) for each partition
    nest = 0                    # nesting level
    start = openRE.search(text, 0)
    if not start:
        return text
    end = closeRE.search(text, start.end())
    next = start
    while end:
        next = openRE.search(text, next.end())
        if not next:            # termination
            while nest:         # close all pending
                nest -= 1
                end0 = closeRE.search(text, end.end())
                if end0:
                    end = end0
                else:
                    break
            spans.append((start.start(), end.end()))
            break
        while end.end() < next.start():
            # { } {
            if nest:
                nest -= 1
                # try closing more
                last = end.end()
                end = closeRE.search(text, end.end())
                if not end:     # unbalanced
                    if spans:
                        span = (spans[0][0], last)
                    else:
                        span = (start.start(), last)
                    spans = [span]
                    break
            else:
                spans.append((start.start(), end.end()))
                # advance start, find next close
                start = next
                end = closeRE.search(text, next.end())
                break           # { }
        if next != start:
            # { { }
            nest += 1
    # collect text outside partitions
    return dropSpans(spans, text)



def dropSpans(spans, text):
    """
    Drop from text the blocks identified in :param spans:, possibly nested.
    """
    spans.sort()
    res = ''
    offset = 0
    for s, e in spans:
        if offset <= s:         # handle nesting
            if offset < s:
                res += text[offset:s]
            offset = e
    res += text[offset:]
    return res



# ----------------------------------------------------------------------
# WikiLinks  modified by lu

# May be nested [[File:..|..[[..]]..|..]], [[Category:...]], etc.
# Also: [[Help:IPA for Catalan|[andora]]]

REImageWikimark = re.compile(r'\|((?:thumb)|(?:border)|(?:frameless)|(?:frame)|(?:thumbnail))\|\w+px\|',re.IGNORECASE)
#[[File:Abraham Lincoln by Nicholas Shepherd, 1846-crop.jpg|thumb|250px|alt=Middle aged clean shaven Lincoln from the hips up.|Lincoln in his 

def replaceInternalLinks_lustyle(text):
    """
    this is modified based on replaceInternalLinks(text) by lu
    Replaces internal links of the form:
    [[title |...|label]]trail

    with title concatenated with trail, when present, e.g. 's' for plural.

    See https://www.mediawiki.org/wiki/Help:Links#Internal_links
    """
    # call this after removal of external links, so we need not worry about
    # triple closing ]]].
    cur = 0
    res = ''
    for s, e in findBalanced(text):
        m = tailRE.match(text, e)#lu: match() strictly require to match from the beginning of text
        if m:
            trail = m.group(0)
            end = m.end()
        else:
            trail = ''
            end = e
        inner = text[s + 2:e - 2]
        # find first |
        pipe = inner.find('|')
        if pipe < 0:
            title = inner
            label = title
        else:
            title = inner[:pipe].rstrip()
            # find last |
            curp = pipe + 1
            
            for s1, e1 in findBalanced(inner):
                last = inner.rfind('|', curp, s1)
                if last >= 0:
                    pipe = last  # advance
                curp = e1
            label = inner[pipe + 1:].strip()
            '''
            lu_BalancedMark = findBalanced(inner)
            lu_flag = False
            for s1, e1 in lu_BalancedMark:
                lu_flag = True
                last = inner.rfind('|', curp, s1)
                if last >= 0:
                    pipe = last  # advance
                curp = e1
            label = inner[pipe + 1:].strip()
                        
            if lu_flag == False:#lu: the block is added by lu
                # original code can proesss: File:Bakunin.png|thumb|upright|Collectivist anarchist [[Mikhail Bakunin]] opposed the [[Marxist]] aim of [[dictatorship of the proletariat]] in favour of universal rebellion, and allied himself with the federalists in the First International before his expulsion by the Marxists.&lt;ref name=bbc/&gt;
                # but failed: US-ASCII code chart.png|thumb|361px|ASCII chart from a 1972 printer manual (b1 is the least significant bit).
                # so, lu modify it.
                pipe = inner.rfind('|', 0, len(inner))
                label = inner[pipe + 1 :].strip()
            '''
 
            
        #lu: the following makeInternalLink are redesigned by lu
        res += text[cur:s] + makeInternalLink_lustyle(title, label) + trail
        cur = end
    return res + text[cur:]

RECategory = re.compile(r':?Category:')
RECategory1 = re.compile(r'\[\[Category:')
REFile = re.compile(r':?File:')
REImage = re.compile(r':?Image:')
#REImage = re.compile(r'(:?Image:)|(double image)')

REImageWikimark_pos = re.compile(r'(?:(?:thumb)|(?:border)|(?:frameless)|(?:frame)|(?:thumbnail))\|',re.IGNORECASE)
REImageWikimark_size = re.compile(r'(?:x?\d+px)\|',re.IGNORECASE)
REImageWikimark_leftright = re.compile(r'(?:(?:lefthey)|(?:left)|(?:upright=?(?:\d+(\.\d+)?)?)|(?:right)|(?:center)|(?:none)|(?:baseline)|(?:sub)|(?:super)|(?:text-top)|(?:middle)|(?:bottom)|(?:text-bottom))\|',re.IGNORECASE)
REImageWikimark_alt = re.compile(r'\|?alt=[^|\]]+\|?',re.IGNORECASE)#lu: this one should be the last

def clearImageFile_pos_alt(label):
    '''
    [[File:Young Lincoln By Charles Keck.JPG|thumb|250px|The young Lincoln in sculpture at Senn Park, Chicago.|alt=A statue of young Lincoln sitting on a stump, holding a book open on his lap]]

    [[File:Abraham Lincoln by Nicholas Shepherd, 1846-crop.jpg|thumb|250px|alt=Middle aged clean shaven Lincoln from the hips up.|Lincoln in his late 30s as a member of the [[U.S. House of Representatives]]. Photo taken by one of Lincoln's law students around 1846.]]

    [[File:Emancipation proclamation.jpg|thumb|250px|Lincoln presents the first draft of the Emancipation Proclamation to his cabinet. Painted by [[Francis Bicknell Carpenter]] in 1864|alt=A dark-haired, bearded, middle-aged man holding documents is seated among seven other men.]]
    
    [[File:US-autism-6-17-1996-2007.png|thumb|left|alt=Bar chart versus time. The graph rises steadily from 1996 to 2007, from about 0.7 to about 5.3. The trend curves slightly upward.|Reports of autism cases per 1,000 children grew dramatically in the US from 1996 to 2007. It is unknown how much, if any, growth came from changes in rates of autism.]]

    lu: for the above example, to clear the irrelevant info(such as thumb, px, alt), only to reserve File label info
    input:
        thumb|250px|The young Lincoln in sculpture at Senn Park, Chicago.|alt=A statue of young Lincoln sitting on a stump, holding a book open on his lap
        thumb|250px|alt=Middle aged clean shaven Lincoln from the hips up.|Lincoln in his late 30s as a member of the [[U.S. House of Representatives]]. Photo taken by one of Lincoln's law students around 1846.
        thumb|250px|Lincoln presents the first draft of the Emancipation Proclamation to his cabinet. Painted by [[Francis Bicknell Carpenter]] in 1864|alt=A dark-haired, bearded, middle-aged man holding documents is seated among seven other men.
    output:
        The young Lincoln in sculpture at Senn Park, Chicago.
        Lincoln in his late 30s as a member of the [[U.S. House of Representatives]]. Photo taken by one of Lincoln's law students around 1846.
        Lincoln presents the first draft of the Emancipation Proclamation to his cabinet. Painted by [[Francis Bicknell Carpenter]] in 1864
    '''
    label = REImageWikimark_pos.sub(r'', label)    
    label = REImageWikimark_size.sub(r'',label)
    label = REImageWikimark_leftright.sub(r'',label)
    label = REImageWikimark_alt.sub(r'', label)
    label = label + ' '
    return label    
    
    

def makeInternalLink_lustyle(title, label):
    # this function is modified based on makeInternalLink(title, label) by lu

    GotoRet = False
    # Anarchism   ,  [[:Category:Anarchism by country|Anarchism by country]]
    #[[Category:Anarchism| ]]
    #[[Category:Political culture]]  
    matchCategory = RECategory.match(title)
    if matchCategory:
        GotoRet = True
    #[[File:Bakunin.png|thumb|upright|Collectivist anarchist [[Mikhail Bakunin]] opposed the [[Marxist]] aim of [[dictatorship of the proletariat]] in favour of universal rebellion, and allied himself with the federalists in the First International before his expulsion by the Marxists.&lt;ref name=bbc/&gt;]]
    matchFile = REFile.match(title)
    if matchFile:
        #for this case, reserve the description for the File.
        if title == label:
            return '' # [[:File:Wiki.png]], its title and lable is same: :File:Wiki.png
        else:
            return clearImageFile_pos_alt(label) #return label
    #[[Image:Levellers declaration and standard.gif|thumb|upright|Woodcut from a [[Diggers]] document by [[William Everard (Digger)|William Everard]]]]
    matchImage = REImage.match(title)
    if matchImage:
        if title == label:
            return ''
        else:
            return clearImageFile_pos_alt(label)#return label
    
           
    if GotoRet == False:
        colon = title.find(':')
        if colon > 0 and title[:colon] not in acceptedNamespaces_lustyle:
            return ''
        if colon == 0:
            # drop also :File:
            colon2 = title.find(':', colon + 1)
            if colon2 > 1 and title[colon + 1:colon2] not in acceptedNamespaces_lustyle:
                return ''
        #if Extractor.keepLinks:
        #    return '<a href="%s">%s</a>' % (quote(title.encode('utf-8')), label)
        #else:
        #   return label
                
                
    if title == label :
        return '[[%s]]' % title
    else:
        return '[[%s|%s]]' % (title, label)
    
    

#-----------------------------------------------------------------------




# ----------------------------------------------------------------------
# WikiLinks

# May be nested [[File:..|..[[..]]..|..]], [[Category:...]], etc.
# Also: [[Help:IPA for Catalan|[andora]]]


def replaceInternalLinks(text):
    """
    Replaces internal links of the form:
    [[title |...|label]]trail

    with title concatenated with trail, when present, e.g. 's' for plural.

    See https://www.mediawiki.org/wiki/Help:Links#Internal_links
    """
    # call this after removal of external links, so we need not worry about
    # triple closing ]]].
    cur = 0
    res = ''
    for s, e in findBalanced(text):
        m = tailRE.match(text, e)#lu: match() strictly require to match from the beginning of text
        if m:
            trail = m.group(0)
            end = m.end()
        else:
            trail = ''
            end = e
        inner = text[s + 2:e - 2]
        # find first |
        pipe = inner.find('|')
        if pipe < 0:
            title = inner
            label = title
        else:
            title = inner[:pipe].rstrip()
            # find last |
            curp = pipe + 1
            for s1, e1 in findBalanced(inner):
                last = inner.rfind('|', curp, s1)
                if last >= 0:
                    pipe = last  # advance
                curp = e1
            label = inner[pipe + 1:].strip()
            
        res += text[cur:s] + makeInternalLink(title, label) + trail
        cur = end
    return res + text[cur:]


# the official version is a method in class Parser, similar to this:
# def replaceInternalLinks2(text):
#     global wgExtraInterlanguageLinkPrefixes

#     # the % is needed to support urlencoded titles as well
#     tc = Title::legalChars() + '#%'
#     # Match a link having the form [[namespace:link|alternate]]trail
#     e1 = re.compile("([%s]+)(?:\\|(.+?))?]](.*)" % tc, re.S | re.D)
#     # Match cases where there is no "]]", which might still be images
#     e1_img = re.compile("([%s]+)\\|(.*)" % tc, re.S | re.D)

#     holders = LinkHolderArray(self)

#     # split the entire text string on occurrences of [[
#     iterBrackets = re.compile('[[').finditer(text)

#     m in iterBrackets.next()
#     # get the first element (all text up to first [[)
#     s = text[:m.start()]
#     cur = m.end()

#     line = s

#     useLinkPrefixExtension = self.getTargetLanguage().linkPrefixExtension()
#     e2 = None
#     if useLinkPrefixExtension:
#         # Match the end of a line for a word that is not followed by whitespace,
#         # e.g. in the case of "The Arab al[[Razi]]",  "al" will be matched
#         global wgContLang
#         charset = wgContLang.linkPrefixCharset()
#         e2 = re.compile("((?>.*[^charset]|))(.+)", re.S | re.D | re.U)

#     if self.mTitle is None:
#         raise MWException(__METHOD__ + ": \self.mTitle is null\n")

#     nottalk = not self.mTitle.isTalkPage()

#     if useLinkPrefixExtension:
#         m = e2.match(s)
#         if m:
#             first_prefix = m.group(2)
#         else:
#             first_prefix = false
#     else:
#         prefix = ''

#     useSubpages = self.areSubpagesAllowed()

#     for m in iterBrackets:
#         line = text[cur:m.start()]
#         cur = m.end()

#         # TODO: Check for excessive memory usage

#         if useLinkPrefixExtension:
#             m = e2.match(e2)
#             if m:
#                 prefix = m.group(2)
#                 s = m.group(1)
#             else:
#                 prefix = ''
#             # first link
#             if first_prefix:
#                 prefix = first_prefix
#                 first_prefix = False

#         might_be_img = False

#         m = e1.match(line)
#         if m: # page with normal label or alt
#             label = m.group(2)
#             # If we get a ] at the beginning of m.group(3) that means we have a link that is something like:
#             # [[Image:Foo.jpg|[http://example.com desc]]] <- having three ] in a row fucks up,
#             # the real problem is with the e1 regex
#             # See bug 1300.
#             #
#             # Still some problems for cases where the ] is meant to be outside punctuation,
#             # and no image is in sight. See bug 2095.
#             #
#             if label and m.group(3)[0] == ']' and '[' in label:
#                 label += ']' # so that replaceExternalLinks(label) works later
#                 m.group(3) = m.group(3)[1:]
#             # fix up urlencoded title texts
#             if '%' in m.group(1):
#                 # Should anchors '#' also be rejected?
#                 m.group(1) = str_replace(array('<', '>'), array('&lt', '&gt'), rawurldecode(m.group(1)))
#             trail = m.group(3)
#         else:
#             m = e1_img.match(line):
#             if m:
#                 # Invalid, but might be an image with a link in its caption
#                 might_be_img = true
#                 label = m.group(2)
#                 if '%' in m.group(1):
#                     m.group(1) = rawurldecode(m.group(1))
#                 trail = ""
#             else:		# Invalid form; output directly
#                 s += prefix + '[[' + line
#                 continue

#         origLink = m.group(1)

#         # Dont allow internal links to pages containing
#         # PROTO: where PROTO is a valid URL protocol these
#         # should be external links.
#         if (preg_match('/^(?i:' + self.mUrlProtocols + ')/', origLink)) {
#             s += prefix + '[[' + line
#             continue
#         }

#         # Make subpage if necessary
#         if useSubpages:
#             link = self.maybeDoSubpageLink(origLink, label)
#         else:
#             link = origLink

#         noforce = origLink[0] != ':'
#         if not noforce:
#             # Strip off leading ':'
#             link = link[1:]

#         nt = Title::newFromText(self.mStripState.unstripNoWiki(link))
#         if nt is None:
#             s += prefix + '[[' + line
#             continue

#         ns = nt.getNamespace()
#         iw = nt.getInterwiki()

#         if might_be_img {	# if this is actually an invalid link
#             if (ns == NS_FILE and noforce) { # but might be an image
#                 found = False
#                 while True:
#                     # look at the next 'line' to see if we can close it there
#                     next_line = iterBrakets.next()
#                     if not next_line:
#                         break
#                     m = explode(']]', next_line, 3)
#                     if m.lastindex == 3:
#                         # the first ]] closes the inner link, the second the image
#                         found = True
#                         label += "[[%s]]%s" % (m.group(0), m.group(1))
#                         trail = m.group(2)
#                         break
#                     elif m.lastindex == 2:
#                         # if there is exactly one ]] that is fine, we will keep looking
#                         label += "[[{m[0]}]]{m.group(1)}"
#                     else:
#                         # if next_line is invalid too, we need look no further
#                         label += '[[' + next_line
#                         break
#                 if not found:
#                     # we couldnt find the end of this imageLink, so output it raw
#                     # but dont ignore what might be perfectly normal links in the text we ve examined
#                     holders.merge(self.replaceInternalLinks2(label))
#                     s += "{prefix}[[%s|%s" % (link, text)
#                     # note: no trail, because without an end, there *is* no trail
#                     continue
#             } else: # it is not an image, so output it raw
#                 s += "{prefix}[[%s|%s" % (link, text)
#                 # note: no trail, because without an end, there *is* no trail
#                      continue
#         }

#         wasblank = (text == '')
#         if wasblank:
#             text = link
#         else:
#             # Bug 4598 madness.  Handle the quotes only if they come from the alternate part
#             # [[Lista d''e paise d''o munno]] . <a href="...">Lista d''e paise d''o munno</a>
#             # [[Criticism of Harry Potter|Criticism of ''Harry Potter'']]
#             #    . <a href="Criticism of Harry Potter">Criticism of <i>Harry Potter</i></a>
#             text = self.doQuotes(text)

#         # Link not escaped by : , create the various objects
#         if noforce and not nt.wasLocalInterwiki():
#             # Interwikis
#             if iw and mOptions.getInterwikiMagic() and nottalk and (
#                     Language::fetchLanguageName(iw, None, 'mw') or
#                     in_array(iw, wgExtraInterlanguageLinkPrefixes)):
#                 # Bug 24502: filter duplicates
#                 if iw not in mLangLinkLanguages:
#                     self.mLangLinkLanguages[iw] = True
#                     self.mOutput.addLanguageLink(nt.getFullText())

#                 s = rstrip(s + prefix)
#                 s += strip(trail, "\n") == '' ? '': prefix + trail
#                 continue

#             if ns == NS_FILE:
#                 if not wfIsBadImage(nt.getDBkey(), self.mTitle):
#                     if wasblank:
#                         # if no parameters were passed, text
#                         # becomes something like "File:Foo.png",
#                         # which we dont want to pass on to the
#                         # image generator
#                         text = ''
#                     else:
#                         # recursively parse links inside the image caption
#                         # actually, this will parse them in any other parameters, too,
#                         # but it might be hard to fix that, and it doesnt matter ATM
#                         text = self.replaceExternalLinks(text)
#                         holders.merge(self.replaceInternalLinks2(text))
#                     # cloak any absolute URLs inside the image markup, so replaceExternalLinks() wont touch them
#                     s += prefix + self.armorLinks(
#                         self.makeImage(nt, text, holders)) + trail
#                 else:
#                     s += prefix + trail
#                 continue

#             if ns == NS_CATEGORY:
#                 s = rstrip(s + "\n") # bug 87

#                 if wasblank:
#                     sortkey = self.getDefaultSort()
#                 else:
#                     sortkey = text
#                 sortkey = Sanitizer::decodeCharReferences(sortkey)
#                 sortkey = str_replace("\n", '', sortkey)
#                 sortkey = self.getConverterLanguage().convertCategoryKey(sortkey)
#                 self.mOutput.addCategory(nt.getDBkey(), sortkey)

#                 s += strip(prefix + trail, "\n") == '' ? '' : prefix + trail

#                 continue
#             }
#         }

#         # Self-link checking. For some languages, variants of the title are checked in
#         # LinkHolderArray::doVariants() to allow batching the existence checks necessary
#         # for linking to a different variant.
#         if ns != NS_SPECIAL and nt.equals(self.mTitle) and !nt.hasFragment():
#             s += prefix + Linker::makeSelfLinkObj(nt, text, '', trail)
#                  continue

#         # NS_MEDIA is a pseudo-namespace for linking directly to a file
#         # @todo FIXME: Should do batch file existence checks, see comment below
#         if ns == NS_MEDIA:
#             # Give extensions a chance to select the file revision for us
#             options = []
#             descQuery = False
#             Hooks::run('BeforeParserFetchFileAndTitle',
#                        [this, nt, &options, &descQuery])
#             # Fetch and register the file (file title may be different via hooks)
#             file, nt = self.fetchFileAndTitle(nt, options)
#             # Cloak with NOPARSE to avoid replacement in replaceExternalLinks
#             s += prefix + self.armorLinks(
#                 Linker::makeMediaLinkFile(nt, file, text)) + trail
#             continue

#         # Some titles, such as valid special pages or files in foreign repos, should
#         # be shown as bluelinks even though they are not included in the page table
#         #
#         # @todo FIXME: isAlwaysKnown() can be expensive for file links; we should really do
#         # batch file existence checks for NS_FILE and NS_MEDIA
#         if iw == '' and nt.isAlwaysKnown():
#             self.mOutput.addLink(nt)
#             s += self.makeKnownLinkHolder(nt, text, array(), trail, prefix)
#         else:
#             # Links will be added to the output link list after checking
#             s += holders.makeHolder(nt, text, array(), trail, prefix)
#     }
#     return holders


def makeInternalLink(title, label):
    colon = title.find(':')
    if colon > 0 and title[:colon] not in acceptedNamespaces:
        return ''
    if colon == 0:
        # drop also :File:
        colon2 = title.find(':', colon + 1)
        if colon2 > 1 and title[colon + 1:colon2] not in acceptedNamespaces:
            return ''
    if Extractor.keepLinks:
        return '<a href="%s">%s</a>' % (quote(title.encode('utf-8')), label)
    else:
        return label


# ----------------------------------------------------------------------
# External links

# from: https://doc.wikimedia.org/mediawiki-core/master/php/DefaultSettings_8php_source.html

wgUrlProtocols = [
    'bitcoin:', 'ftp://', 'ftps://', 'geo:', 'git://', 'gopher://', 'http://',
    'https://', 'irc://', 'ircs://', 'magnet:', 'mailto:', 'mms://', 'news:',
    'nntp://', 'redis://', 'sftp://', 'sip:', 'sips:', 'sms:', 'ssh://',
    'svn://', 'tel:', 'telnet://', 'urn:', 'worldwind://', 'xmpp:', '//'
]

# from: https://doc.wikimedia.org/mediawiki-core/master/php/Parser_8php_source.html

# Constants needed for external link processing
# Everything except bracket, space, or control characters
# \p{Zs} is unicode 'separator, space' category. It covers the space 0x20
# as well as U+3000 is IDEOGRAPHIC SPACE for bug 19052
EXT_LINK_URL_CLASS = r'[^][<>"\x00-\x20\x7F\s]'
ANCHOR_CLASS = r'[^][\x00-\x08\x0a-\x1F]'
ExtLinkBracketedRegex = re.compile(
    '\[(((?i)' + '|'.join(wgUrlProtocols) + ')' + EXT_LINK_URL_CLASS + r'+)' +
    r'\s*((?:' + ANCHOR_CLASS + r'|\[\[' + ANCHOR_CLASS + r'+\]\])' + r'*?)\]',
    re.S | re.U)
# A simpler alternative:
# ExtLinkBracketedRegex = re.compile(r'\[(.*?)\](?!])')

EXT_IMAGE_REGEX = re.compile(
    r"""^(http://|https://)([^][<>"\x00-\x20\x7F\s]+)
    /([A-Za-z0-9_.,~%\-+&;#*?!=()@\x80-\xFF]+)\.((?i)gif|png|jpg|jpeg)$""",
    re.X | re.S | re.U)


def replaceExternalLinks(text):
    """
    https://www.mediawiki.org/wiki/Help:Links#External_links
    [URL anchor text]
    """
    s = ''
    cur = 0
    for m in ExtLinkBracketedRegex.finditer(text):
        s += text[cur:m.start()]
        cur = m.end()

        url = m.group(1)
        label = m.group(3)

        # # The characters '<' and '>' (which were escaped by
        # # removeHTMLtags()) should not be included in
        # # URLs, per RFC 2396.
        # m2 = re.search('&(lt|gt);', url)
        # if m2:
        #     link = url[m2.end():] + ' ' + link
        #     url = url[0:m2.end()]

        # If the link text is an image URL, replace it with an <img> tag
        # This happened by accident in the original parser, but some people used it extensively
        m = EXT_IMAGE_REGEX.match(label)
        if m:
            label = makeExternalImage(label)

        # Use the encoded URL
        # This means that users can paste URLs directly into the text
        # Funny characters like ö aren't valid in URLs anyway
        # This was changed in August 2004
        s += makeExternalLink(url, label)  # + trail

    return s + text[cur:]


def makeExternalLink(url, anchor):
    """Function applied to wikiLinks"""
    if Extractor.keepLinks:
        return '<a href="%s">%s</a>' % (quote(url.encode('utf-8')), anchor)
    else:
        return anchor


def makeExternalImage(url, alt=''):
    if Extractor.keepLinks:
        return '<img src="%s" alt="%s">' % (url, alt)
    else:
        return alt


def replaceExternalLinks_lustyle(text):
    """
    modified based on replaceExternalLinks(text) by lu
    https://www.mediawiki.org/wiki/Help:Links#External_links
    [URL anchor text]
    
    LU: for the external links, I decide to remove the url, but reserve its label
    """
    s = ''
    cur = 0
    for m in ExtLinkBracketedRegex.finditer(text):
        s += text[cur:m.start()]
        cur = m.end()

        url = m.group(1)
        label = m.group(3)

        # # The characters '<' and '>' (which were escaped by
        # # removeHTMLtags()) should not be included in
        # # URLs, per RFC 2396.
        # m2 = re.search('&(lt|gt);', url)
        # if m2:
        #     link = url[m2.end():] + ' ' + link
        #     url = url[0:m2.end()]

        # If the link text is an image URL, replace it with an <img> tag
        # This happened by accident in the original parser, but some people used it extensively
        m = EXT_IMAGE_REGEX.match(label)
        if m:
            label = makeExternalImage_lustyle(label)

        # Use the encoded URL
        # This means that users can paste URLs directly into the text
        # Funny characters like ö aren't valid in URLs anyway
        # This was changed in August 2004
        s += makeExternalLink_lustyle(url, label)  # + trail

    return s + text[cur:]


def makeExternalLink_lustyle(url, anchor):
    """this funciton is modeified based on makeExternalLink by lu
    for the external link, I think it is useless, so only reserve its anchor and discard its url info.    
    """
    """Function applied to wikiLinks"""
    """
    if Extractor.keepLinks:
        return '<a href="%s">%s</a>' % (quote(url.encode('utf-8')), anchor)
    else:
        return anchor
    """
    return anchor
    


def makeExternalImage_lustyle(url, alt=''):
    """this funciton is modeified based on makeExternalImage by lu
    for the external image, I think it is useless, so only reserve its alt and discard its url info.    
    """
    """
    if Extractor.keepLinks:
        return '<img src="%s" alt="%s">' % (url, alt)
    else:
        return alt
    """
    return alt
    

# ----------------------------------------------------------------------

# match tail after wikilink
tailRE = re.compile('\w+')

syntaxhighlight = re.compile('&lt;syntaxhighlight .*?&gt;(.*?)&lt;/syntaxhighlight&gt;', re.DOTALL)

# skip level 1, it is page name level
section = re.compile(r'(==+)\s*(.*?)\s*\1')

listOpen = {'*': '<ul>', '#': '<ol>', ';': '<dl>', ':': '<dl>'}
listClose = {'*': '</ul>', '#': '</ol>', ';': '</dl>', ':': '</dl>'}
listItem = {'*': '<li>%s</li>', '#': '<li>%s</<li>', ';': '<dt>%s</dt>',
            ':': '<dd>%s</dd>'}


def compact(text):
    """Deal with headers, lists, empty sections, residuals of tables.
    :param text: convert to HTML.
    """

    page = []             # list of paragraph
    headers = {}          # Headers for unfilled sections
    emptySection = False  # empty sections are discarded
    listLevel = []        # nesting of lists

    for line in text.split('\n'):

        if not line:
            continue
        # Handle section titles
        m = section.match(line) #section = re.compile(r'(==+)\s*(.*?)\s*\1')
        if m:
            title = m.group(2)
            lev = len(m.group(1)) # header level
            if Extractor.toHTML:
                page.append("<h%d>%s</h%d>" % (lev, title, lev))
            if title and title[-1] not in '!?':
                title += '.'    # terminate sentence.
            headers[lev] = title
            # drop previous headers
            for i in list(headers.keys()):
                if i > lev:
                    del headers[i]
            emptySection = True
            listLevel = []
            continue
        # Handle page title
        elif line.startswith('++'):
            title = line[2:-2]
            if title:
                if title[-1] not in '!?':
                    title += '.'
                page.append(title)
        # handle indents
        elif line[0] == ':':
            # page.append(line.lstrip(':*#;'))
            continue
        # handle lists
        elif line[0] in '*#;:':
            i = 0
            # c: current level char
            # n: next level char
            for c, n in zip_longest(listLevel, line, fillvalue=''):
                if not n or n not in '*#;:': # shorter or different
                    if c:
                        if Extractor.toHTML:
                            page.append(listClose[c])
                        listLevel = listLevel[:-1]
                        continue
                    else:
                        break
                # n != ''
                if c != n and (not c or (c not in ';:' and n not in ';:')):
                    if c:
                        # close level
                        if Extractor.toHTML:
                            page.append(listClose[c])
                        listLevel = listLevel[:-1]
                    listLevel += n
                    if Extractor.toHTML:
                        page.append(listOpen[n])
                i += 1
            n = line[i - 1]  # last list char
            line = line[i:].strip()
            if line:  # FIXME: n is '"'
                if Extractor.keepLists:
                    # emit open sections
                    items = sorted(headers.items())
                    for i, v in items:
                        page.append(v)
                    headers.clear()
                    # FIXME: use item count for #-lines
                    bullet = '1. ' if n == '#' else '- '
                    page.append('{0:{1}s}'.format(bullet, len(listLevel)) + line)
                elif Extractor.toHTML:
                    page.append(listItem[n] % line)
        elif len(listLevel):
            page.append(line)
            if Extractor.toHTML:
                for c in reversed(listLevel):
                    page.append(listClose[c])
            listLevel = []

        # Drop residuals of lists
        elif line[0] in '{|' or line[-1] == '}':
            continue
        # Drop irrelevant lines
        elif (line[0] == '(' and line[-1] == ')') or line.strip('.-') == '':
            continue
        elif len(headers):
            if Extractor.keepSections:
                items = sorted(headers.items())
                for i, v in items:
                    page.append(v)
            headers.clear()
            page.append(line)  # first line
            emptySection = False
        elif not emptySection:
            # Drop preformatted
            if line[0] != ' ':  # dangerous
                page.append(line)

    return page


def handle_unicode(entity):
    numeric_code = int(entity[2:-1])
    if numeric_code >= 0x10000: return ''
    return chr(numeric_code)


def compact_lustyle(text):
    """
    the function is modified based on compact(text) by lu
    for Lustyle, we don't need so many HTML encode.
    
    Deal with headers, lists, empty sections, residuals of tables.
    :param text: convert to HTML.
    """

    page = []             # list of paragraph
    headers = {}          # Headers for unfilled sections
    emptySection = False  # empty sections are discarded
    listLevel = []        # nesting of lists

    for line in text.split('\n'):

        if not line:
            continue
        # Handle section titles
        m = section.match(line)
        #print 'line:%s' % line
        if m:  #lu: ==See also==
            title = m.group(2)
            lev = len(m.group(1)) # header level
            
            if Extractor.LUstyle == False: # this seems odd, only for compatible with original code
                if Extractor.toHTML:# this is original code of author
                    page.append("<h%d>%s</h%d>" % (lev, title, lev))
            else: #lu:for LUstyle, I decide to reserve the html mark of section title
                page.append("<h%d>%s</h%d>" % (lev, title, lev))

            if title and title[-1] not in '!?':
                title += '.'    # terminate sentence.
            headers[lev] = title
            # drop previous headers
            for i in list(headers.keys()):
                if i > lev:
                    del headers[i]
            emptySection = True
            listLevel = []
            continue
        # Handle page title
        elif line.startswith('++'):
            title = line[2:-2]
            if title:
                if title[-1] not in '!?':
                    title += '.'
                page.append(title)
        # handle indents
        elif line[0] == ':':
            if Extractor.LUstyle == False:
                #lu: the follow two lines are the original codes of author
                # page.append(line.lstrip(':*#;'))
                continue  #this means delete the content of : indent
            else:
                #lu: in our style, we reserve the indent content by :
                page.append(line[1:])#  :The Sino-Soviet split was one of the key events of the Cold War, equal in importance to the construction of the Berlin Wall, the Cuban Missile Crisis, the Second Vietnam War, and Sino-American rapprochement.  The split helped to determine the framework of the Second Cold War in general, and influenced the course of the Second Vietnam War in particular.<ref>{{cite book|author=Lorenz M. Lüthi|title=The Sino-Soviet Split: Cold War in the Communist World|url=https://books.google.com/books?id=dl4TRDxqexMC|year=2010|publisher=Princeton UP|page=1}}</ref>
        # handle lists
        elif line[0] in '*#;:': #lu: all of them are corresponding with lists.  https://www.mediawiki.org/wiki/Help:Formatting
            i = 0
            # c: current level char
            # n: next level char
            for c, n in zip_longest(listLevel, line, fillvalue=''):#lu:zip_longest('ABCD', 'xy', fillvalue='-') --> Ax By C- D-
                if not n or n not in '*#;:': # shorter or different
                    if c:
                        if Extractor.LUstyle == False:  # for Lustyle, we don't reserve list mark.                      
                            if Extractor.toHTML: #lu: this is original code of author
                                 page.append(listClose[c])
                        else:
                            pass

                        listLevel = listLevel[:-1]
                        continue
                    else:
                        break
                # n != ''
                if c != n and (not c or (c not in ';:' and n not in ';:')):
                    if c:
                        # close level
                        if Extractor.LUstyle == False: #for Lustyle, we don't reserve list mark.
                            if Extractor.toHTML:#lu: this is original code of author
                                page.append(listClose[c])
                        else:
                            pass

                        listLevel = listLevel[:-1]
                    listLevel += n       #lu: #REDIRECT [[Main Page]]\r, # is correpsonding with 'Numbered list'
                    
                    if Extractor.LUstyle == False:# for Lustyle, we don't reserve list mark
                        if Extractor.toHTML:#lu: this is original code of author
                            page.append(listOpen[n])
                    else:
                        pass

                i += 1
            n = line[i - 1]  # last list char
            line = line[i:].strip()
            if line:  # FIXME: n is '"'
                if Extractor.keepLists:
                    # emit open sections
                    items = sorted(headers.items())
                    for i, v in items:
                        page.append(v)
                    headers.clear()
                    # FIXME: use item count for #-lines
                    bullet = '1. ' if n == '#' else '- '
                    page.append('{0:{1}s}'.format(bullet, len(listLevel)) + line)
                #elif Extractor.toHTML:  #lu: this is original code of author
                #    page.append(listItem[n] % line)
                elif Extractor.LUstyle: #lu: the above keepLists seems well, I take it 
                    # emit open sections
                    #items = sorted(headers.items())
                    #for i, v in items:
                    #    page.append(v)
                    #headers.clear()
                    # FIXME: use item count for #-lines
                    bullet = '1. ' if n == '#' else '- '
                    page.append('{0:{1}s}'.format(bullet, len(listLevel)) + line)
                elif Extractor.toHTML:
                    page.append(listItem[n] % line)
                    
                    
        elif len(listLevel):
            page.append(line)
            
            if Extractor.LUstyle == False: #for Lustyle, I don't reserve html mark of list           
                if Extractor.toHTML: # this is original code of author
                    for c in reversed(listLevel):
                        page.append(listClose[c])
            else:
                pass

            listLevel = []

        # Drop residuals of lists
        elif line[0] in '{|' or line[-1] == '}':
            continue
        # Drop irrelevant lines
        elif (line[0] == '(' and line[-1] == ')') or line.strip('.-') == '':
            continue
        elif len(headers):
            if Extractor.LUstyle == False:
                if Extractor.keepSections:#lu: this is original code of author
                    items = sorted(headers.items())
                    for i, v in items:
                        page.append(v)
            else:#lu: the above keepLists seems well, I take it 
                #items = sorted(headers.items())
                #for i, v in items:
                #    page.append(v)
                pass

            headers.clear()
            page.append(line)  # first line
            emptySection = False
        elif not emptySection:
            # Drop preformatted
            if line[0] != ' ':  # dangerous
                page.append(line) #lu: \r, https://www.mediawiki.org/wiki/Help:Links\r, [skype:echo123 call me]\r
                                  #lu: [[:Category:Help]]\r, Wikipedia\r, 

    return page

# ------------------------------------------------------------------------------
# Output


class NextFile(object):
    """
    Synchronous generation of next available file name.
    """

    filesPerDir = 100

    def __init__(self, path_name):
        self.path_name = path_name
        self.dir_index = -1
        self.file_index = -1

    def __next__(self):
        self.file_index = (self.file_index + 1) % NextFile.filesPerDir
        if self.file_index == 0:
            self.dir_index += 1
        dirname = self._dirname()
        if not os.path.isdir(dirname):
            os.makedirs(dirname)
        return self._filepath()

    next = __next__

    def _dirname(self):
        char1 = self.dir_index % 26
        char2 = self.dir_index // 26 % 26
        return os.path.join(self.path_name, '%c%c' % (ord('A') + char2, ord('A') + char1))

    def _filepath(self):
        return '%s/wiki_%02d' % (self._dirname(), self.file_index)


class OutputSplitter(object):
    """
    File-like object, that splits output to multiple files of a given max size.
    """

    def __init__(self, nextFile, max_file_size=0, compress=True):
        """
        :param nextFile: a NextFile object from which to obtain filenames
            to use.
        :param max_file_size: the maximum size of each file.
        :para compress: whether to write data with bzip compression.
        """
        self.nextFile = nextFile
        self.compress = compress
        self.max_file_size = max_file_size
        self.file = self.open(next(self.nextFile))

    def reserve(self, size):
        if self.file.tell() + size > self.max_file_size:
            self.close()
            self.file = self.open(next(self.nextFile))

    def write(self, data):
        self.reserve(len(data))
        self.file.write(data)

    def close(self):
        self.file.close()

    def open(self, filename):
        if self.compress:
            return bz2.BZ2File(filename + '.bz2', 'w')
        else:
            return open(filename, 'wb')


# ----------------------------------------------------------------------
# READER

tagRE = re.compile(r'(.*?)<(/?\w+)[^>]*>(?:([^<]*)(<.*?>)?)?')
#                    1     2               3      4

tagRE_redirect_lu = re.compile(r'(.*?)<redirect title="([^"]*?)" />')  #eg. <redirect title="Ashmore and Cartier Islands" />
#                                1                     2

tagRE_category_lu = re.compile(r'\[\[Category:([^\|]+)(\| )?\]\](.*?)')#eg.[[Category:Anarchism| ]],  [[Category:Presentation layer protocols]]</text>
#                                             1       2         3
   
def load_templates(file, output_file=None):
    """
    Load templates from :param file:.
    :param output_file: file where to save templates and modules.
    """
    global templateNamespace, templatePrefix
    templatePrefix = templateNamespace + ':'
    global moduleNamespace, modulePrefix
    modulePrefix = moduleNamespace + ':'
    if output_file:
        output = codecs.open(output_file, 'wb', 'utf-8')
    for page_count, page_data in enumerate(pages_from(file)):
        id, revid, title, ns, page = page_data
        if not output_file and (not templateNamespace or
                                not moduleNamespace):  # do not know it yet
            # reconstruct templateNamespace and moduleNamespace from the first title
            if ns in templateKeys:
                colon = title.find(':')
                if colon > 1:
                    if ns == '10':
                        templateNamespace = title[:colon]
                        templatePrefix = title[:colon + 1]
                    elif ns == '828':
                        moduleNamespace = title[:colon]
                        modulePrefix = title[:colon + 1]
        if ns in templateKeys:
            text = ''.join(page)
            define_template(title, text)
            # save templates and modules to file
            if output_file:
                output.write('<page>\n')
                output.write('   <title>%s</title>\n' % title)
                output.write('   <ns>%s</ns>\n' % ns)
                output.write('   <id>%s</id>\n' % id)
                output.write('   <text>')
                for line in page:
                    output.write(line)
                output.write('   </text>\n')
                output.write('</page>\n')
        if page_count and page_count % 100000 == 0:
            logging.info("Preprocessed %d pages", page_count)
    if output_file:
        output.close()
        logging.info("Saved %d templates to '%s'", len(templates), output_file)


def pages_from(input):
    """
    Scans input extracting pages.
    :return: (id, revid, title, namespace key, page), page is a list of lines.
    :return by Lu, (id, revid, title, ns, page, redirect_title_lu, category_lu). page, redirect_title_lu, category_lu is a list of lines.
    """
    # we collect individual lines, since str.join() is significantly faster
    # than concatenation
    page = []#lu: [] means page is a LIST
    id = None#lu: None means 'NULL' in other language.
    ns = '0'
    last_id = None
    revid = None
    inText = False #lu: a flag. whether current line lies in <text>...</text>
    redirect = False
    redirect_title_lu = None #lu: added by wenpenglu, used to record the title of redirect page.
    title = None    
    category_lu = []#lu: save the categories of current page    
    for line in input:
        #logging.info("lu:line no.%d",input.filelineno())
        line = line.decode('utf-8') #lu: convert the text to unicode
        
        #logging.info(line)
        if '<' not in line:  # faster than doing re.search()
            if inText:
                page.append(line)
                #here 1-th to add category_lu. there are three place to process category
                m_c_lu = tagRE_category_lu.match(line) #lu: match() requires to match from the begin 
                if m_c_lu:
                    cat = m_c_lu.group(1)
                    category_lu.append(cat)                
                
            continue
        
        
        m = tagRE.search(line)#tagRE = re.compile(r'(.*?)<(/?\w+)[^>]*>(?:([^<]*)(<.*?>)?)?')                              #                    1     2               3      4
        if not m:
            continue
        tag = m.group(2)
        if tag == 'page': #lu: 'true' means to read a new wiki page/concept.
            page = []
            redirect = False
            redirect_title_lu = None
        elif tag == 'id' and not id:
            id = m.group(3)
        elif tag == 'id' and id:
            revid = m.group(3)
        elif tag == 'title':
            title = m.group(3)
        elif tag == 'ns':
            ns = m.group(3)
        elif tag == 'redirect':
            redirect = True
            #lu: if this line is as: <redirect title="Aviation" />, so record the title and the redirect title
            m_lu = tagRE_redirect_lu.search(line)
            if not m_lu:
                logging.info("lu: ERROR!ERROR!ERROR! failed to process redirect line:%s",line)
                continue
            redirect_title_lu = m_lu.group(2)
        elif tag == 'text':#lu: 'true' means that it begins to process <text>...</text>, in which there may be many lines
            if m.lastindex == 3 and line[m.start(3)-2] == '/': # self closing
                # <text xml:space="preserve" />
                continue
            inText = True
            line = line[m.start(3):m.end(3)]#lu: cut out the content of the 3-th group of 'm'
            page.append(line)
            if m.lastindex == 4:  # open-close
                inText = False
        elif tag == '/text':#lu: 'true' means that it finishes to process <text>...</text>. the last line of <text>...<./text> is as follow: ***</text>, such as:[[Category:Far-left politics]]</text>
            if m.group(1):
                page.append(m.group(1))
            inText = False
            #here 2-th to add category_lu. there are three place to process category
            m_c_lu = tagRE_category_lu.match(line) #lu: match() requires to match from the begin 
            if m_c_lu:
                cat = m_c_lu.group(1)
                category_lu.append(cat)
        elif inText:
            page.append(line)
            #here 3-th to add category_lu. there are three place to process category
            m_c_lu = tagRE_category_lu.match(line) #lu: match() requires to match from the begin 
            if m_c_lu:
                cat = m_c_lu.group(1)
                category_lu.append(cat)
        elif tag == '/page':#lu: 'true' means a wiki page/concept has been read.
            """#this code block is the original edition of author
            if id != last_id and not redirect:
                yield (id, revid, title, ns, page)#lu:!!!this is an important function, it makes 'page_from(input)' become a generator. here, it will generate wiki page information.
                last_id = id
                ns = '0'
            """         
            if id != last_id:
                yield (id, revid, title, ns, page, redirect_title_lu, category_lu)#lu:!!!this is an important function, it makes 'page_from(input)' become a generator. here, it will generate wiki page information.
                last_id = id
                ns = '0'
            id = None
            revid = None
            title = None
            page = []
            category_lu = []


def process_dump(input_file, template_file, out_file, file_size, file_compress,
                 process_count):
    """
    :param input_file: name of the wikipedia dump file; '-' to read from stdin
    :param template_file: optional file with template definitions.
    :param out_file: directory where to store extracted data, or '-' for stdout
    :param file_size: max size of each extracted file, or None for no max (one file)
    :param file_compress: whether to compress files with bzip.
    :param process_count: number of extraction processes to spawn.
    """
    global urlbase
    global knownNamespaces
    global templateNamespace, templatePrefix
    global moduleNamespace, modulePrefix

    if input_file == '-':
        input = sys.stdin #lu: input by console
    else:
        input = fileinput.FileInput(input_file, openhook=fileinput.hook_compressed)#lu:fileinput is another "fileinput.py", in which there is a class named as "FileInput"

    # collect siteinfo   #lu:collect information of site
    for line in input:#lu: 'input' is an fileinput object, is it iterate automatically?
        line = line.decode('utf-8')#lu: the char is stored with Unicode in Python. so, need to convert "utf-8" to "Unicode"
        m = tagRE.search(line)#lu: tarRE: tagRE = re.compile(r'(.*?)<(/?\w+)[^>]*>(?:([^<]*)(<.*?>)?)?')
        if not m:
            continue
        tag = m.group(2)
        if tag == 'base': #lu: the correspondin line is "    <base>https://en.wikipedia.org/wiki/Main_Page</base>"
            # discover urlbase from the xml dump file
            # /mediawiki/siteinfo/base
            base = m.group(3)
            urlbase = base[:base.rfind("/")]
        elif tag == 'namespace':#lu: the corresponding line is "      <namespace key="-2" case="first-letter">Media</namespace>"
            knownNamespaces.add(m.group(3))
            if re.search('key="10"', line):
                templateNamespace = m.group(3)
                templatePrefix = templateNamespace + ':'
            elif re.search('key="828"', line):
                moduleNamespace = m.group(3)
                modulePrefix = moduleNamespace + ':'
        elif tag == '/siteinfo':#lu: read "/siteinfo", then quit the loop.
            break

    if Extractor.expand_templates:#lu: the class of Extractor set the attribute true defaultly.
        # preprocess
        template_load_start = default_timer()#lu: get system time
        if template_file:#lu: the parameter of the current function. I don't have the file.
            if os.path.exists(template_file):
                logging.info("Preprocessing '%s' to collect template definitions: this may take some time.", template_file)
                # can't use with here:'
                file = fileinput.FileInput(template_file,
                                         openhook=fileinput.hook_compressed)
                load_templates(file)
                file.close()
            else:
                if input_file == '-':
                    # can't scan then reset stdin; must error w/ suggestion to specify template_file
                    raise ValueError("to use templates with stdin dump, must supply explicit template-file")
                logging.info("Preprocessing '%s' to collect template definitions: this may take some time.", input_file)
                load_templates(input, template_file)
                input.close()
                input = fileinput.FileInput(input_file, openhook=fileinput.hook_compressed)
        template_load_elapsed = default_timer() - template_load_start #lu: record the time to load template
        logging.info("Loaded %d templates in %.1fs", len(templates), template_load_elapsed)

    # process pages
    logging.info("Starting page extraction from %s.", input_file)
    extract_start = default_timer()#lu: record the begin time to extract wiki dump

    # Parallel Map/Reduce:
    # - pages to be processed are dispatched to workers #lu: 
    # - a reduce process collects the results, sort them and print them. #lu:

    maxsize = 10 * process_count
    # output queue
    output_queue = Queue(maxsize=maxsize)#lu: FIFO duilie. https://blog.linuxeye.com/334.html | Queue is a function in multiprocessing in Python  
    maxsizetitlecollect_lu = 10000
    output_queue_redirect_title_lu = Queue(maxsizetitlecollect_lu)#lu: the data in this Queue is short, so we give it a bigger value. set it as "max_spool_length = 10000"
    output_queue_itrnc = Queue(maxsizetitlecollect_lu)#lu: put (id,title,redirect_title_lu,ns,category) into output_queue_itrnc,which would be received by lu_reduce_process_itrnc.


    if out_file == '-':#lu:the parameter of current function
        out_file = None

    worker_count = max(1, process_count)

    # load balancing    #在向output_queue放入元素前，会检查这个spool_length的大小。避免其装入过多，消耗大量内存资源
    max_spool_length = 10000
    spool_length = Value('i', 0, lock=False)#lu: Value is a function in multiprocessing in Python  https://docs.python.org/2/library/multiprocessing.html#multiprocessing.Value
                                            #lu:这里作者将lock置为false，这个spool_length对象将不会被Lock，这在多线程编程中感觉并不安全。有可能是因为作者后期只创建了一个reduce进程，而且spool_length的操作都在这个进程内部。
    
    
    # reduce job that sorts and prints output
    reduce = Process(target=reduce_process,#lu: "Process" is a funtion provided by Python, "reduce_process" is a function in current file.
                     args=(output_queue, spool_length,#lu: as descibed in former,"a reduce process collects the results, sort them and print them."
                           out_file, file_size, file_compress))#lu: these are the parameters of "reduce_process()"
    reduce.start() #lu: Python use "Process()" to create object of process(jincheng) and use "start()" to start the process. However, the code of "reduce_proecess" function will not be executed in this step.

    # reduce job that collect Redirect titles
    # this code block used to write redirect information to a disk file.
    reduce_collectRedirectTitle = Process(target=lu_reduce_process_collectRedirectTitle,
                                          args=(output_queue_redirect_title_lu,out_file,))
    reduce_collectRedirectTitle.start()
    #reduce job that collect all of (id, title, redirect_title, ns)  itrn
    reduce_collect_itrnc = Process(target=lu_reduce_process_itrnc,
                                  args=(output_queue_itrnc,out_file,))
    reduce_collect_itrnc.start()
    
    
    

    # initialize jobs queue
    jobs_queue = Queue(maxsize=maxsize)#lu: to get a Queue(duilie) object   


    # start worker processes
    logging.info("Using %d extract processes.", worker_count)
    workers = []
    for i in range(worker_count):
        extractor = Process(target=extract_process,#lu: "Process" is a funtion provided by Python, "reduce_process" is a function in current file.
                            args=(i, jobs_queue, output_queue))
        extractor.daemon = True  # only live while parent process lives
        extractor.start()
        workers.append(extractor)

    # Mapper process
    page_num = 0
    for page_data in pages_from(input):#lu: pages_from is a function in current file, which scan input to get (id, revid, title, ns, page)
                                        #lu: the following code, reduce process and extract proess will execute with pages_from() simultaneously
        #id, revid, title, ns, page = page_data
        id, revid, title, ns, page, redirect_title_lu, category_lu = page_data
        
        
        #this code block used to put (id,title,redirect_title_lu,ns, category_lu) into output_queue_itrnc,which
        #would be received by lu_reduce_process_itrnc. the later reduce process will write it to disk file.
        #1. the (id,title,redirect_title_lu,ns, category_lu) is send to output_queue_itrnc
        #2. lu_reduce_process_itrnc process get a tuple from output_queue_itrnc, write it to disk file.
        if True:
            delay=0
            if output_queue_itrnc.qsize()>=max_spool_length:
                while output_queue_itrnc.qsize > max_spool_length/10:
                    time.sleep(5)
                    delay += 5
                if delay:
                    logging.info('Delay %ds',delay)
            output_itrnc = (id, title, redirect_title_lu, ns, category_lu)
            output_queue_itrnc.put(output_itrnc)
            logging.info('process_dump put output_itrnc (id:%s title:%s redirect_title_lu:%s ns:%s category:%s) into output_queue_itrn, whose \
size become:%d',output_itrnc[0],output_itrnc[1],output_itrnc[2],output_itrnc[3],'; '.join(output_itrnc[4]),output_queue_itrnc.qsize())

        
        
        #this code block used to put redirect information into output_queue_redirect_title_lu, which 
        #would be received by lu_reduce_process_collectRedirectTitle. the later reduce process will write it to disk file.
        #1. the (id,title,redirect_titie) is send to output_queue_redirect_title_lu
        #2. lu_reduce_process_collectRedirectTitle process get a tuple from output_queue_redirect_title_lu, write it to disk file.
        if redirect_title_lu:#lu: if there is a redirect title , it need to be saved
            delay = 0
            # this is coding by lu, which is not good as "if keepPage(ns, page)". 
            # if need to control read speed, please see "if keepPage(ns, page)".
            # but, lu's code also can control read speed.
            if output_queue_redirect_title_lu.qsize() >= max_spool_length:
                while output_queue_redirect_title_lu.qsize() > max_spool_length/10:
                    time.sleep(5)
                    delay += 5
            if delay:
                logging.info('Delay %ds', delay)      
            output_redirect_title_lu = (id, title, redirect_title_lu)
            output_queue_redirect_title_lu.put(output_redirect_title_lu) #put output data on the Queue, then reduce process will receive it.
            logging.info("process_dump put output_redirect_title_lu\
(id:%s title:%s redirect_title_lu:%s) into output_queue_redirect_title_lu, whose size become:%d",\
                id,title, redirect_title_lu, output_queue_redirect_title_lu.qsize())
        
        
        if Lustyle == False:
            #this code block is original edit of author. 
            #1.the papge is send to jobs_queue
            #2.the worker process(extract) get a job from jobs_queue, process it, then send the result to output_queue
            #3.the reduce process:
            #3.1  if the target next_page in spool, write it to disk file
            #3.2  else get a page from output_queue and put it into spool
            if (not redirect_title_lu) and keepPage(ns, page):
            #if keepPage(ns, page):#lu: according to ns and page, to judge whether the page should be kept or discarded?
                # slow down
                delay = 0
                if spool_length.value > max_spool_length:#lu:???? is this to judge the fu_zai_cheng_du of spool? the max value is 10000. 这里作者应该是打算，如果spool中的页面数多于10000了，就暂且停一下，不要再继续往里放数据。这应该也可以避免内存无限增大吧。
                    # reduce to 10% #lu:if spool_length is too high, sleep untile it reduces to 10%
                    while spool_length.value > max_spool_length/10:
                        time.sleep(10)
                        delay += 10
                if delay:
                    logging.info('Delay %ds', delay)
                job = (id, revid, title, page, page_num)#lu: one wiki page is corresponding with a job. this is a prepared job (a prepared article information).  "page_num" is the count of being processed pages.
                jobs_queue.put(job) # goes to any available extract_process #lu: put it to jobs_queue, it would be processed by a free "extractor" process.
                logging.info("process_dump put job(id:%s title:%s page_num:%d) into jobs_queue. current jobs_queue's size:%d", id, title, page_num, jobs_queue.qsize());
                page_num += 1
                
                ###############################
                #logging.info('this code block is only for test, it must be deleted when running');
                
                #extract_process(1, jobs_queue, output_queue)
                ###############################
        else:
            if (not redirect_title_lu) and keepPage_lu(ns, title, page):
            #if keepPage(ns, page):#lu: according to ns and page, to judge whether the page should be kept or discarded?
                # slow down
                delay = 0
                if spool_length.value > max_spool_length:#lu:???? is this to judge the fu_zai_cheng_du of spool? the max value is 10000. 这里作者应该是打算，如果spool中的页面数多于10000了，就暂且停一下，不要再继续往里放数据。这应该也可以避免内存无限增大吧。
                    # reduce to 10% #lu:if spool_length is too high, sleep untile it reduces to 10%
                    while spool_length.value > max_spool_length/10:
                        time.sleep(10)
                        delay += 10
                if delay:
                    logging.info('Delay %ds', delay)
                job = (id, revid, title, page, page_num)#lu: one wiki page is corresponding with a job. this is a prepared job (a prepared article information).  "page_num" is the count of being processed pages.
                jobs_queue.put(job) # goes to any available extract_process #lu: put it to jobs_queue, it would be processed by a free "extractor" process.
                logging.info("process_dump put job(id:%s title:%s page_num:%d) into jobs_queue. current jobs_queue's size:%d", id, title, page_num, jobs_queue.qsize());
                page_num += 1
                   
        
        page = None             # free memory #lu: page is a [], where are a lot of lines, to free it.

    input.close()

    logging.info("process_dump all pages in 'input' file has been put into jobs_queue!")
    # signal termination
    for _ in workers:
        jobs_queue.put(None) #lu: "None" means to  add end-of-queue markers
    # wait for workers to terminate
    logging.info("process_dump has put 'None' into jobs_queue, wait for workers(extract_process) to terminate") 
    for w in workers:
        w.join() #lu: this means "Wait until child process terminates"

    # signal end of work to reduce process
    output_queue.put(None)  #lu: "None" means to  add end-of-queue markers
    # wait for it to finish
    logging.info("process_dump has put 'None' into output_queue, wait for reduce(reduce_process) to terminate") 
    reduce.join()
    
    #signal end of work to lu_reduce_process_collectRedirectTitle
    output_queue_redirect_title_lu.put(None)
    #wait for it to finish
    logging.info("process_dump has put 'None' into output_queue_redirect_title_lu, wait for reduce(lu_reduce_process_collectRedirectTitle) to terminate") 
    reduce_collectRedirectTitle.join()
    
    #signal end of work to lu_reduce_process_itrn
    output_queue_itrnc.put(None)
    #wait for it to finish
    logging.info("process_dump has put 'None' into output_queue_itrn, wait for reduce(lu_reduce_process_itrn) to terminate")
    reduce_collect_itrnc.join()
    
    

    extract_duration = default_timer() - extract_start
    extract_rate = page_num / extract_duration
    logging.info("Finished %d-process extraction of %d articles in %.1fs (%.1f art/s)",
                 process_count, page_num, extract_duration, extract_rate)
    
    logging.info("Finished reduce,reduce_collectRedirectTitle,reduce_collect_itrn Processes")


# ----------------------------------------------------------------------
# Multiprocess support


def extract_process(i, jobs_queue, output_queue):
    """Pull tuples of raw page content, do CPU/regex-heavy fixup, push finished text
    :param i: process id.
    :param jobs_queue: where to get jobs.
    :param output_queue: where to queue extracted text for output.
    """
    logging.info("enter %d-th extract_process pid:%d",i,os.getpid());
    out = StringIO()                 # memory buffer
    while True:
        logging.info("extract_process pid:%d 'while True' try to get a job from jobs_queue and put result into output_queue. current jobs_queue's size:%d", os.getpid(), jobs_queue.qsize())
        job = jobs_queue.get()  # job is (id, title, page, page_num)
                                #lu : jobs_queue.get() would block current extract process, until it can return a job object.
        if job:
            id, revid, title, page, page_num = job
            logging.info("extract_process pid:%d get a job(id:%s title:%s page_num:%s) from jobs_queue to extract... jobs_queue's size become:%d", os.getpid(), id, title, page_num, jobs_queue.qsize())
            try:
                e = Extractor(*job[:4]) # (id, revid, title, page)#lu: Extractor is a CLASS, this is to get a instance of the class
                page = None              # free memory
                e.extract(out)  #lu: call the method of "extract". this is the key to process the content of text
                text = out.getvalue()
            except:
                text = ''
                logging.exception('Processing page: %s %s', id, title)
                
            output_queue.put((page_num, text))
            logging.info("extract_process pid:%d the job(id:%s title:%s page_num:%s) has been extracted and put result into output_queue, whose size become:%d", os.getpid(), id, title, page_num, output_queue.qsize())
            out.truncate(0)
            out.seek(0)
        else:
            logging.info("extract_process pid:%d the job gotten from job_queue is 'None', so to quit...",os.getpid())
            logging.debug('Quit extractor')
            break
    out.close()
    
    
def lu_reduce_process_itrnc(output_queue_itrnc, outputdir):
    '''
    The module get a tuple(id, title, redirect_title, ns, category), and write it to disk file
    :param output_queue_itrnc: the Queue of tuple(id, title, redirect_title, ns, category). the Queue is produced by 'def process_dump()'
    Notice: the module only be run by ONE process. because it includes a file write operation.
    '''
    logging.info("enter lu_reduce_process_itrnc pid:%d",os.getpid())
    filename = 'id_title_redirect_ns_category.txt'
    
    if outputdir:
        if outputdir[len(outputdir)-1] == '/':
            filename = outputdir + filename
        else:
            filename = outputdir + '/' + filename    
    
    f = open(filename,'wb')
    while True:
        pair = output_queue_itrnc.get()
        if not pair:
            break
        id, title, redirect_title, ns, category = pair
        
        logging.info("lu_reduce_process_itrnc pid:%d get a pair(%s,%s,%s,%s,%s) to write from output_queue_itrnc, whose size become %d",os.getpid(),pair[0],pair[1],pair[2],pair[3],'; '.join(category),output_queue_itrnc.qsize())
        if not redirect_title:
            redirect_title='NONENULL'
        
        line = '{}\t{}\t{}\t{}\t{}\t\n'.format(id,title,redirect_title,ns,'; '.join(category))
        f.write(line.encode('utf-8'))
    
    
    f.close()
    logging.info("quit lu_reduce_process_itrnc pid:%d",os.getpid())
    
    

    
def lu_reduce_process_collectRedirectTitle(output_queue_redirect_title_lu, outputdir):
    '''
    the module get a tuple(id,title,redirect_title) from the Queue(output_queue_redirect_title_lu)
    :param output_queue_redirect_title_lu: the Queue of tuple(id,title,redirect_title). the Queue is produced by 'def process_dump()'
    Notice: the module only be run by ONE process. because it includes a file write operation.
    '''
    logging.info("enter lu_reduce_process_collectRedirectTitle  pid:%d ",os.getpid())
    filename = "id_title_redirecttile.txt"
    if outputdir:
        if outputdir[len(outputdir)-1] == '/':
            filename = outputdir + filename
        else:
            filename = outputdir + '/' + filename
        
    f = open(filename, 'wb')
    while True:
        pair = output_queue_redirect_title_lu.get()
        if not pair:
            break
        id, title, redirect_title = pair
        logging.info("lu_reduce_process_collectRedirectTitle pid:%d get a pair(%s,%s,%s) to write from output_queue_redirect_title_lu, whose size become %d",os.getpid(),pair[0],pair[1],pair[2],output_queue_redirect_title_lu.qsize())
        #ready to write the data into a file
        line = '{}\t{}\t{}\n'.format(id,title,redirect_title)
        f.write(line.encode('utf-8'))
        
    f.close()    
    logging.info("quit lu_reduce_process_collectRedirectTitle  pid:%d ",os.getpid())
    


report_period = 10000           # progress report period
def reduce_process(output_queue, spool_length,
                   out_file=None, file_size=0, file_compress=True):
    """Pull finished article text, write series of files (or stdout)
    :param output_queue: text to be output.
    :param spool_length: spool length.
    :param out_file: filename where to print.
    :param file_size: max file size.
    :param file_compress: whether to compress output.
    """
    logging.info("enter reduce_process pid:%d",os.getpid())
    if out_file:
        nextFile = NextFile(out_file)
        output = OutputSplitter(nextFile, file_size, file_compress)
    else:
        output = sys.stdout if PY2 else sys.stdout.buffer
        if file_compress:
            logging.warn("writing to stdout, so no output compression (use an external tool)")
    
    interval_start = default_timer()
    # FIXME: use a heap
    spool = {}        # collected pages
    next_page = 0     # sequence numbering of page
    while True:
        logging.info("reduce_process pid:%d 'while True' try to find next_page:%d from spool or put new pair into spool. current spool:%s",os.getpid(),next_page,spool.keys())
        if next_page in spool:#lu: whether "next_page" lies in "spool". this can confirm that the page is written to file sequentially.
            logging.info("reduce_process pid:%d successs to find (next_page:%s) to write from spool. current spool:%s", os.getpid(), next_page,spool.keys())
            lu_readytowrite = spool.pop(next_page).encode('utf-8')#lu:pop the specified "next_page" from spool
            output.write(lu_readytowrite)
            #output.write(spool.pop(next_page).encode('utf-8'))
            logging.info("reduce_process pid:%d write %d-th page(text:%s) into output file, current spool:%s ", os.getpid(), next_page, lu_readytowrite[0:20], spool.keys())
            next_page += 1
            # tell mapper our load:
            spool_length.value = len(spool)
            # progress report
            if next_page % report_period == 0:
                interval_rate = report_period / (default_timer() - interval_start)
                logging.info("Extracted %d articles (%.1f art/s)",
                             next_page, interval_rate)
                interval_start = default_timer()
        else:
            # mapper puts None to signal finish
            logging.info("reduce_process pid:%d failed to find (next_page:%s) from spool. current spool:%s",os.getpid(), next_page, spool.keys())
            logging.info("reduce_process pid:%d try to get a new pair to put into spool from output_queue. current spool:%s current output_queue's size:%d", os.getpid(), spool.keys(), output_queue.qsize())
            pair = output_queue.get() #lu: the process would be blocked until suceecess to get a pair from output_queue.
            if not pair:
                logging.info("reduce_process pid:%d check output_queue.get(), failed to get a pair from output_queue, is that 'None'?, so to break. output_queue's size become:%d",os.getpid(), output_queue.qsize());
                break
            page_num, text = pair
            logging.info("reduce_process pid:%d check output_queue.get(), success to get a pair, ready to put it into spoll. output_queue's size become:%d",os.getpid(), output_queue.qsize())
            spool[page_num] = text
            logging.info("reduce_process pid:%d put the pair[page_num:%d,text:%s] into spool. current spool:%s", os.getpid(), page_num, text[0:20], spool.keys())
            # tell mapper our load:
            spool_length.value = len(spool)
            # FIXME: if an extractor dies, process stalls; the other processes
            # continue to produce pairs, filling up memory.
            if len(spool) > 200:
                logging.debug('Collected %d, waiting: %d, %d', len(spool),
                              next_page, next_page == page_num)
    if output != sys.stdout:
        output.close()
    logging.info("quit reduce_process pid:%d",os.getpid())


# ----------------------------------------------------------------------

# Minimum size of output files
minFileSize = 200 * 1024

def main():
    global urlbase, acceptedNamespaces, filter_disambig_pages
    global templateCache
    global Lustyle #this is added by luwpeng

    parser = argparse.ArgumentParser(prog=os.path.basename(sys.argv[0]),
                                     formatter_class=argparse.RawDescriptionHelpFormatter,
                                     description=__doc__)
    parser.add_argument("input",
                        help="XML wiki dump file")
    groupO = parser.add_argument_group('Output')#lu:groupO is the first set of parameters. look readme.MD
    groupO.add_argument("-o", "--output", default="text",
                        help="directory for extracted files (or '-' for dumping to stdout)")
    groupO.add_argument("-b", "--bytes", default="1M",
                        help="maximum bytes per output file (default %(default)s)",
                        metavar="n[KMG]")
    groupO.add_argument("-c", "--compress", action="store_true",
                        help="compress output files using bzip")

    groupP = parser.add_argument_group('Processing')#lu:groupP is the second set of parameters. look readme.MD
    groupP.add_argument("--html", action="store_true",
                        help="produce HTML output, subsumes --links")
    groupP.add_argument("--lustyle", action="store_true",#lu: added by lu. if use this, the value of "args.lustyle" would be 'True'
                        help="produce output, as --html. But, reserve more information")    
    groupP.add_argument("-l", "--links", action="store_true",
                        help="preserve links")
    groupP.add_argument("-s", "--sections", action="store_true",
                        help="preserve sections")
    groupP.add_argument("--lists", action="store_true",
                        help="preserve lists")
    groupP.add_argument("-ns", "--namespaces", default="", metavar="ns1,ns2",
                        help="accepted namespaces in links")
    groupP.add_argument("--templates",
                        help="use or create file containing templates")
    groupP.add_argument("--no-templates", action="store_false",
                        help="Do not expand templates")
    groupP.add_argument("-r", "--revision", action="store_true", default=Extractor.print_revision,
                        help="Include the document revision id (default=%(default)s)")
    groupP.add_argument("--min_text_length", type=int, default=Extractor.min_text_length,
                        help="Minimum expanded text length required to write document (default=%(default)s)")
    groupP.add_argument("--filter_disambig_pages", action="store_true", default=filter_disambig_pages,
                        help="Remove pages from output that contain disabmiguation markup (default=%(default)s)")
    default_process_count = cpu_count() - 1
    parser.add_argument("--processes", type=int, default=default_process_count,
                        help="Number of processes to use (default %(default)s)")                
    

    groupS = parser.add_argument_group('Special')#lu:groupS is the third set of parameters. look readme.MD
    groupS.add_argument("-q", "--quiet", action="store_true",
                        help="suppress reporting progress info")
    groupS.add_argument("--debug", action="store_true",
                        help="print debug info")
    groupS.add_argument("-a", "--article", action="store_true",
                        help="analyze a file containing a single article (debug option)")
    groupS.add_argument("-v", "--version", action="version",
                        version='%(prog)s ' + version,
                        help="print program version")

    args = parser.parse_args()#lu: to parese the command and get arg parameters.
          #lu:Extractor is a "Class" in current wikiExtractor.py file.
    Extractor.keepLinks = args.links#lu: to set the attribute of Extractor according to args.
    Extractor.keepSections = args.sections
    Extractor.keepLists = args.lists
    Extractor.toHTML = args.html
    Extractor.print_revision = args.revision
    Extractor.min_text_length = args.min_text_length
    if args.html:
        Extractor.keepLinks = True
        
    Extractor.LUstyle = args.lustyle#added by lu
    if args.lustyle:
        args.no_templates = False #lu: don't to expand the templates
    if args.lustyle:
        #Extractor.english_stopwords = stopwords.words('english')  #the stopwords of nltk can work on virtual machine, but fails on UTS cluster. so Change it
        Extractor.english_stopwords =['i','me','my','myself','we','our','ours','ourselves','you','your','yours','yourself','yourselves','he','him','his','himself','she','her','hers','herself','it','its','itself','they','them','their','theirs','themselves','what','which','who','whom','this','that','these','those','am','is','are','was','were','be','been','being','have','has','had','having','do','does','did','doing','a','an','the','and','but','if','or','because','as','until','while','of','at','by','for','with','about','against','between','into','through','during','before','after','above','below','to','from','up','down','in','out','on','off','over','under','again','further','then','once','here','there','when','where','why','how','all','any','both','each','few','more','most','other','some','such','no','nor','not','only','own','same','so','than','too','very','s','t','can','will','just','don','should','now','d','ll','m','o','re','ve','y','ain','aren','couldn','didn','doesn','hadn','hasn','haven','isn','ma','mightn','mustn','needn','shan','shouldn','wasn','weren','won','wouldn']

    Extractor.expand_templates = args.no_templates
    filter_disambig_pages = args.filter_disambig_pages#lu: the left is a global variable

    Lustyle = args.lustyle

    try:
        power = 'kmg'.find(args.bytes[-1].lower()) + 1#lu:"KMG" is a input para to adjust the size of output file
        file_size = int(args.bytes[:-1]) * 1024 ** power
        if file_size < minFileSize:#lu:minFileSize's default value is 200K
            raise ValueError()
    except ValueError:
        logging.error('Insufficient or invalid size: %s', args.bytes)
        return

    if args.namespaces:
        acceptedNamespaces = set(args.namespaces.split(','))

    FORMAT = '%(levelname)s: %(message)s'
    logging.basicConfig(format=FORMAT)#lu: logging is a module provided by python

    logger = logging.getLogger()
    if not args.quiet:
        logger.setLevel(logging.INFO)
    if args.debug:
        logger.setLevel(logging.DEBUG)

    input_file = args.input #lu: get the file path of inputted

    if not Extractor.keepLinks:
        ignoreTag('a') #lu: don't keep the hyperlink <a> mark?  is there is <a> mark?

    # sharing cache of parser templates is too slow:
    # manager = Manager()
    # templateCache = manager.dict()

    if args.article:#lu: if the command requires to process a article 
        if args.templates:
            if os.path.exists(args.templates):
                with open(args.templates) as file:
                    load_templates(file)

        file = fileinput.FileInput(input_file, openhook=fileinput.hook_compressed)
        for page_data in pages_from(file):
            #id, revid, title, ns, page = page_data #original code of author. (id, revid, title, namespace key, page)
            id, revid, title, ns, page, _ , _ = page_data #lu: (id, revid, title, ns, page, redirect_title_lu, category_lu)
            Extractor(id, revid, title, page).extract(sys.stdout)
        file.close()
        return

    output_path = args.output
    if output_path != '-' and not os.path.isdir(output_path):
        try:
            os.makedirs(output_path)
        except:
            logging.error('Could not create: %s', output_path)
            return

    process_dump(input_file, args.templates, output_path, file_size,
                 args.compress, args.processes)#lu: the former codes in main() is to prepare for this line.


if __name__ == '__main__':
    #logging.info("TEST befor main()")
    #reduce_process(None,None)
    main()
