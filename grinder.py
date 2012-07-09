#!/usr/bin/env python
"""grinder - Git repository data miner

Usage: grinder.py [-hd FILE] [--quiet | --verbose] <command>

Options:
  -h, --help      show this screen
  --version       show version
  -s, --sorted    sorted output
  -d, --db=<db>   database name to store results [default: db.sqlite]
  --quite         print less text
  --verbose       print more text

"""

from __future__ import division
from __future__ import unicode_literals
from __future__ import print_function

import os, sys, re
import tempfile
import logging
import sqlite3

from docopt import docopt
from optparse import OptionParser
from pygit2 import *
from datetime import datetime
from time import strptime, mktime
from os.path import splitext, exists
from collections import defaultdict
from itertools import tee, izip, izip_longest, product
from jellyfish import levenshtein_distance
from lapacho import hungarian

#from models import setup

from storm.locals import *
from storm.expr import *
from storm.tracer import debug

regexp = {
    'bug_number': re.compile(r'bug[# \t]*(\d+)'),
    'bracket_number': re.compile(r'\[(\d+)\]'),
    'issue_number': re.compile(r'\#(\d+)'),
    'sentence': re.compile(r'(?:Fixes|Closes|Resolves) issue \#?(\d+)'),
    #'plain_number': re.compile(r'(\d+)'),
    #'keyword': re.compile(r'(?:fix(?:e[ds])?|bugs?|defects?|patch)'),
}

FORMAT = '%(asctime)-15s %(message)s'
logging.basicConfig(format=FORMAT)
logger = logging.getLogger('grinder')

def test_regexp(string):
    for key, pattern in regexp.items():
        m = pattern.search(string)
        if not m:
            continue
        return [int(g) for g in m.groups()]
    return []

class File(Storm):

    __storm_table__ = 'files'

    id = Int(name='file_id', allow_none=False, primary=True)
    path = Unicode(allow_none=False)

    def __init__(self, path):
        self.path = path

    @classmethod
    def getone(cls, store, **args):
        if args.has_key('path'):
            one = store.get(File, File.path == args['path'])
            if not one: one = File(args['path'])
            return one


class Commit(Storm):

    __storm_table__ = 'commits'

    id = Int(name='commit_id', allow_none=False, primary=True)
    hex = Unicode(allow_none=False)
    date = Int()
    #files = ReferenceSet(Commit.id,
    #                     'CommitFile.commit_id',
    #                     'CommitFile.file_id',
    #                     File.id)
    edits = ReferenceSet('Commit.id', 'Edit.commit_id')
    parents = ReferenceSet('Commit.id',
                           'CommitCommit.child_id',
                           'CommitCommit.parent_id',
                           'Commit.id')

    def __init__(self, hex, date):
        self.hex = hex
        self.date = date

    @classmethod
    def getone(cls, **args):
        if args.has_key('hex'):
            one = store.get(Commit, args['hex'])
            if not one: one = Commit(args['hex'])
            return one


#class CommitFile(Storm):
#    __storm_table__ = 'commits_files'
#    __storm_primary__ = 'commit_id', 'file_id'
#    commit_id = Int()
#    file_id = Int()


class CommitCommit(Storm):

    __storm_table__ = 'commits_commits'
    __storm_primary__ = 'parent_id', 'child_id'

    parent_id = Int(allow_none=False)
    child_id = Int(allow_none=False)


class Edit(Storm):

    __storm_table__ = 'edits'

    id = Int(name='edit_id', allow_none=False, primary=True)
    old_file_id = Int()
    old_file = Reference(old_file_id, 'File.id')
    new_file_id = Int()
    new_file = Reference(new_file_id, 'File.id')
    old_line = Int()
    new_line = Int()
    commit_id = Int(allow_none=False)
    commit = Reference(commit_id, 'Commit.id')

    def __init__(self, commit, old_file, new_file, old_no, new_no):
        self.commit = commit
        self.old_file = old_file
        self.new_file = new_file
        self.old_line = old_no
        self.new_line = new_no


class Bug(Storm):

    __storm_table__ = 'bugs'

    id = Int(name='bug_id', allow_none=None, primary=True)
    bug_no = Int(allow_none=False)
    commits = ReferenceSet('Bug.id',
                           'BugCommit.bug_id',
                           'BugCommit.commit_id',
                           'Commit.id')

    def __init__(self, bug_no):
        self.bug_no = bug_no

    @classmethod
    def getone(cls, store, **args):
        if args.has_key('no'):
            one = store.get(Bug, Bug.bug_no == args['no'])
            if not one:
                one = store.add(Bug(args['no']))
                store.flush()
            return one


class BugCommit(Storm):

    __storm_table__ = 'bugs_commits'
    __storm_primary__ = 'bug_id', 'commit_id'

    bug_id = Int(allow_none=False)
    commit_id = Int(allow_none=False)


def setup(database_path):
    database = create_database('sqlite:%s' % database_path)
    store = Store(database)

    # Setup database
    store.execute('''
      PRAGMA recursive_triggers = TRUE
      ''')

    # Create tables
    store.execute('''
      CREATE TABLE IF NOT EXISTS files(
          file_id INTEGER PRIMARY KEY AUTOINCREMENT,
          path TEXT NOT NULL UNIQUE
      )
      ''', noresult=True)
    store.execute('''
      CREATE TABLE IF NOT EXISTS commits(
          commit_id INTEGER PRIMARY KEY AUTOINCREMENT,
          --oid BLOB NOT NULL,
          hex TEXT NOT NULL UNIQUE,
          date INTEGER NOT NULL
      )
      ''', noresult=True)
    store.execute('''
      CREATE TABLE IF NOT EXISTS commits_commits(
          parent_id INTEGER,
          child_id INTEGER,
          PRIMARY KEY (parent_id, child_id)
      )
      ''', noresult=True)
    store.execute('''
      CREATE TABLE IF NOT EXISTS edits(
          edit_id INTEGER PRIMARY KEY AUTOINCREMENT,
          old_file_id INTEGER REFERENCES files(file_id),
          new_file_id INTEGER REFERENCES files(file_id),
          old_line INTEGER,
          new_line INTEGER,
          commit_id INTEGER REFERENCES commits(commit_id)
      )
      ''', noresult=True)
    store.execute('''
      CREATE TABLE IF NOT EXISTS bugs(
          bug_id INTEGER PRIMARY KEY AUTOINCREMENT,
          bug_no INTEGER
      )
      ''', noresult=True)
    store.execute('''
      CREATE TABLE IF NOT EXISTS bugs_commits(
          bug_id INTEGER REFERENCES bugs(bug_id),
          commit_id INTEGER REFERENCES commits(commit_id),
          PRIMARY KEY (bug_id, commit_id)
      )
      ''', noresult=True)

    # Create indeces
    store.execute('''CREATE INDEX IF NOT EXISTS commits_hex_index ON commits(hex)''')
    store.execute('''CREATE INDEX IF NOT EXISTS edits_old_file_index ON edits(old_file_id)''')
    store.execute('''CREATE INDEX IF NOT EXISTS edits_new_file_index ON edits(new_file_id)''')
    store.execute('''CREATE INDEX IF NOT EXISTS edits_commit_index ON edits(commit_id)''')
    store.execute('''CREATE INDEX IF NOT EXISTS bugs_commits_bug_index ON bugs(bug_id)''')
    store.execute('''CREATE INDEX IF NOT EXISTS bugs_commits_commits_index ON commits(commit_id)''')

    # Commit all changes
    store.commit()

    return store


def build(repo, store, options):
    for c in repo.walk(repo.head.oid, GIT_SORT_REVERSE):
        logger.info('commit %s', c.hex)

        # Store commit
        commit = store.find(Commit, Commit.hex == c.hex.decode('utf-8')).one()
        if commit is None:
            commit = store.add(Commit(c.hex.decode('utf-8'), c.commit_time))
        store.flush()

        # Check commit message
        for i in test_regexp(c.message):
            bug = store.find(Bug, Bug.bug_no == i).one()
            if not bug: bug = store.add(Bug(i))
            bug.commits.add(commit)

            logger.debug('bug %d', i)

            store.flush()

        # Check parents
        for p in c.parents:
            parent = store.find(Commit, Commit.hex == p.hex.decode('utf-8')).one()
            if parent is None:
                parent = store.add(Commit(p.hex.decode('utf-8'), p.commit_time))
            commit.parents.add(parent)

            logger.debug('parent %s', p.hex)

            diff = p.tree.diff(c.tree)
            if 'hunks' not in diff.changes:
                continue

            for h in [f for f in diff.changes['hunks'] if splitext(f.old_file)[1] in ['.c', '.h']]:
                old_file = store.find(File, File.path == h.old_file.decode('utf-8')).one()
                if old_file is None:
                    old_file = store.add(File(h.old_file.decode('utf-8')))
                new_file = store.find(File, File.path == h.new_file.decode('utf-8')).one()
                if new_file is None:
                    new_file = store.add(File(h.new_file.decode('utf-8')))
                store.flush()

                old_data = [l for l in h.data if l[1] != GIT_DIFF_LINE_ADDITION]
                new_data = [l for l in h.data if l[1] != GIT_DIFF_LINE_DELETION]

                logger.debug('hunk old:%d-%d, new:%d-%d', h.old_start, h.old_lines, h.new_start, h.new_lines)

                deletions = [(l[0], i) for i, l in enumerate(old_data) if l[1] == GIT_DIFF_LINE_DELETION]
                additions = [(l[0], i) for i, l in enumerate(new_data) if l[1] == GIT_DIFF_LINE_ADDITION]

                # Identify changed lines
                changed_lines = []
                if len(deletions) != 0 and len(additions) != 0:
                    d = map(lambda (x, y): levenshtein_distance(x[0], y[0], True), product(deletions, additions))
                    step = len(additions)
                    matrix = [d[x:x+step] for x in xrange(0, len(d), step)]

                    indexes = hungarian(matrix)
                    changed_lines = [(deletions[i][1], additions[j][1]) for i, j in indexes if 0.0 < matrix[i][j] and matrix[i][j] < 0.4]

                # Store all changed lines
                for x, y in changed_lines:
                    store.add(Edit(commit, old_file, new_file, h.old_start + x, h.new_start + y))

                # Store all deleted lines
                for l, x in deletions:
                    if x not in [i for i, j in changed_lines]:
                        store.add(Edit(commit, old_file, new_file, h.old_start + x, None))

                # Store all added lines
                for l, y in additions:
                    if y not in [j for i, j in changed_lines]:
                        store.add(Edit(commit, old_file, new_file, None, h.new_start + y))

                store.flush()

        # Save the changes
        store.commit()

def process(repo, store, options):
    expressions = [ True == True ] # studid Storm
    if options.from_date is not None:
        expressions += [ Commit.date >= mktime(strptime(options.from_date, "%d/%m/%Y")) ]
    if options.to_date is not None:
        expressions += [ Commit.date <= mktime(strptime(options.to_date, "%d/%m/%Y")) ]

    for bug in store.find(Bug):
        patches = set()
        for commit in bug.commits.find(And(expressions)):
            #PreviousEdit = ClassAlias(Edit)
            #edits = Select(Edit.id, Edit.commit_id == commit.id)
            #result = store.find((Commit, PreviousEdit),
            #                   Commit.id == PreviousEdit.commit_id,
            #                   (PreviousEdit.new_file_id == Edit.old_file_id) &
            #                   (PreviousEdit.new_line == Edit.old_line) &
            #                   (Commit.date < commit.date) &
            #                   Edit.id.is_in(edits))
            #patches = set([c[0] for c in result])

            for edit in commit.edits:
                origin = [Commit, Join(Edit, Edit.commit_id == Commit.id)]
                result = store.using(*origin).find(Commit,
                            (Commit.date < commit.date) &
                            (Edit.new_file_id == edit.old_file_id) &
                            (Edit.new_line == edit.old_line))
                c = result.order_by(Desc(Commit.date)).first()
                if c: patches.add(c)

        if len(patches) != 0:
            print('#%s [%s]\n' % (bug.bug_no, ', '.join(['%s' % c.hex for c in patches])))


def parse_from_date(option, opt_str, value, parser):
    parser.values.from_date = mktime(strptime(value, "%d/%m/%Y"))


def parse_to_date(option, opt_str, value, parser):
    parser.values.to_date = mktime(strptime(value, "%d/%m/%Y"))


def main():
    #args = docopt(__doc__, argv=sys.argv[1:], help=True, version='0.1.0')

    parser = OptionParser(usage="usage: %prog [options] path")
    parser.add_option('-d', '--database',
            metavar="FILE", dest="database", default="db.sqlite",
            help="store to database [default: %default]")
    parser.add_option('', '--from',
            metavar="DATE", dest="from_date",
            help="only consider commits from date")
    parser.add_option('', '--to',
            metavar="DATE", dest="to_date",
            help="only consider commits to date")
    parser.add_option('-n', '--depth',
            metavar="N", dest="depth", default=1,
            help="depth for recursive search [default: %default]")
    parser.add_option('-b', '--build',
            action="store_true", dest="build", default=False,
            help="build database using repository content")
    parser.add_option('-q', '--quiet',
            action="store_false", dest="verbose",
            help="be less verbose")
    parser.add_option('-v', '--verbose',
            action="store_true", dest="verbose", default=False,
            help="be more verbose")

    (options, args) = parser.parse_args()
    if len(args) != 1:
        parser.error("incorrect number of arguments")

    path = args[0]
    if not exists(path):
        parser.error("invalid path argument")

    store = setup(options.database)
    repo = Repository(path)

    logger.setLevel(logging.DEBUG)

    if options.build:
        build(repo, store, options)
    process(repo, store, options)

    store.close()

if __name__ == '__main__':
    main()
