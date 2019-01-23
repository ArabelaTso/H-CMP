# -*- coding: utf-8 -*-
# @Author  : arabela

import os
import re
import time
import copy
import subprocess
import collections
import pandas as pd
import multiprocessing
from shutil import copyfile
from sklearn.externals import joblib


def split_back(stmt):
    if not stmt:
        return (set(), '')
    parts = stmt.split(',')
    if len(parts) == 2:
        return (set([parts[0]]), parts[1])
    elif len(parts) == 3:
        return (set([parts[0], parts[1]]), parts[2])
    else:
        print('Wrong rule')


def split_string_to_tuple(stmt):
    if not stmt:
        return (set(), '')
    try:
        parts = stmt.split(' -> ')
    except ValueError:
        print('Error string: %s' % stmt)
    else:
        if not len(re.findall(' & ', parts[0])):
            return (set([parts[0]]), parts[1])
        else:
            return (set(parts[0].split(' & ')), parts[1])


class DataProcess(object):
    def __init__(self, name, replace_index):
        self.name = name
        self.replace_index = replace_index

    def execute(self, save=True, load=False):
        # if load:
        #     try:
        #         return joblib.load("%s/data/dataset.pkl" % self.name), joblib.load("%s/itemMeaning.pkl" % self.name)
        #     except:
        #         raise FileExistsError
        dataList, stateDict = self.collect_dataset()
        para_digit = self.para_form(stateDict.keys())
        dataset, itemMeaning = self.encode(dataList, stateDict)
        print('Reachable set: %d' % len(dataset))

        if save:
            if not os.path.exists("{}/data".format(self.name)):
                os.mkdir("{}/data".format(self.name))
            joblib.dump(dataset, "{}/data/dataset.pkl".format(self.name))
            joblib.dump(itemMeaning, "{}/data/itemMeaning.pkl".format(self.name))
        print('size of dataset: {} * {}'.format(len(dataset), len(dataset[0])))
        return dataset, itemMeaning, para_digit  # df, itemMeaning

    def para_form(self, name_list):
        """
        the parameter the protocol uses
        with symmetry reduction: NODE_1, NODE_2, ...
        without: 1, 2, ...
        '[]' is a symbol of local variables
        :param name_list:
        :return:
        """
        for name in name_list:
            if '[' in name:
                return False if re.search(r'\w+\_\d', name) else True
            continue
        return True

    def collect_dataset(self):
        """
        From reachable set collect dataset
        :return:
        dataList:
            [
                [v1, v2, ..., vn],
                [e11, e12, ..., e1n],
                ...,
                [en1,en2, ..., enn]]
        dataDict:
            {v1: {e11,e21,..., en1}, v2: {e12,e22, ..., en2},...}
        """
        print('Reading reachable set')
        if not os.path.exists('{0}/{0}.csv'.format(self.name)) and not os.path.exists('{0}/{0}.txt'.format(self.name)):
            raise FileExistsError
        if not os.path.exists('{0}/{0}.csv'.format(self.name)) or not self.is_rs_match_dataset():
            return self.txt2csv()
        else:
            return self.readcsv()

    def is_rs_match_dataset(self):
        """
        Counts the number of states in reachable set printed by Murphi and the number of lines in transferred csv.
        If these two equal, return True; else return False

        NOTE: actually csv file will add a title line with variable names, so # states in txt +1 = # lines in csv
        """
        print('call is_rs_match_dataset')
        if not os.path.exists('{0}/{0}.txt'.format(self.name)):
            print('Cannot find reachable state set file. \nNot sure whether the reachable set matches the protocol.')
            return True

        csv_cnt = subprocess.check_output(['wc', '-l', '{0}/{0}.csv'.format(self.name)]).decode('utf-8')
        tail_rs = subprocess.check_output(['tail', '{0}/{0}.txt'.format(self.name)]).decode('utf-8')
        return int(re.findall(r'\d+', csv_cnt)[0]) == int(
            re.findall(r'State Space Explored:.*?(\d+)\sstates', tail_rs, re.S)[0]) + 1

    def readcsv(self):
        print('call read_csv')
        df = pd.read_csv('{0}/{0}.csv'.format(self.name))
        stateDict = {}
        booleandf = set(df.select_dtypes(include=[bool]).columns.values)

        for col in df.columns:
            if col in booleandf:
                df[col] = df[col].map({True: 'true', False: 'false'})
            stateDict[col] = set(df[col])
        return [df.columns.tolist()] + df.values.tolist(), stateDict

    def txt2csv(self):
        print('txt2csv...')
        csv_filename = '{0}/{0}.csv'.format(self.name)

        reachset = open('{0}/{0}.txt'.format(self.name)).read()

        if self.replace_index:
            for k, v in self.replace_index.items():
                reachset = reachset.replace(k, v)
        states = re.findall(r'State\s\d+:\n(.*?)\n\n', reachset, re.S)

        variables = [var.split(':')[0] for var in states[0].split('\n')]

        dataset = [variables]
        open(csv_filename, 'w').write("{}\n".format("".join(variables)))

        stateDict = collections.defaultdict(set)

        for state in states:
            for var in state.split('\n'):
                stateDict[var.split(":")[0]].add(var.split(":")[1])
            # dataset.append([var for var in state.split('\n')])
            dataset.append([var.split(':')[1] for var in state.split('\n')])

        with open(csv_filename, 'w') as f:
            for line in dataset:
                f.write(','.join(line) + '\n')
        return dataset, stateDict

    def describe(self, dataList):
        print('---------------------')
        print('Protocol {} has {} states.'.format(self.name, len(dataList) - 1))
        print('Each state has {} variables.'.format(len(dataList[0])))
        print('---------------------\n')

    def encode(self, dataList, stateDict):
        has_atom = os.path.exists('{0}/atom.txt'.format(self.name))
        dataset, itemMeaning = self.tonumber(dataList, stateDict, atom=has_atom, neg=False)

        return dataset, itemMeaning

    def tonumber(self, stateList, statesDict, atom=False, neg=False):
        if atom:
            stateList, statesDict = self.atom_feature(statesDict, stateList, self.get_atoms())
            mappingDict, itemMeaning = self.states2num_atom(statesDict)
            # states_numberful = self.mapStates(mappingDict, stateList)
        elif neg:
            stateList, statesDict = self.negative(stateList, statesDict)
            mappingDict, itemMeaning = self.states2num(statesDict)
            # states_numberful = self.mapStates(mappingDict, stateList)
        else:
            mappingDict, itemMeaning = self.states2num(statesDict)
        states_numberful = self.mapStates(mappingDict, stateList)

        return states_numberful, itemMeaning

    def enumerateStates(self, stateslist):
        statesDict = collections.defaultdict(set)
        col = len(stateslist[0])
        row = len(stateslist)
        for c in range(col):
            for r in range(1, row):
                if (stateslist[r][c] not in statesDict[stateslist[0][c]]) and (stateslist[r][c] != 'Undefined'):
                    statesDict[stateslist[0][c]].add(stateslist[r][c])
        return statesDict

    def atom_feature(self, stateDict, stateList, atom_feature):
        new_statelist, new_stateDict = [], {}
        index = {title: i for i, title in enumerate(stateList[0])}
        print('index of atomic predicates:', index)

        for i, af in enumerate(atom_feature):
            pre = af.split(' ')[0]
            post = af.split(' ')[-1]
            if pre not in index:
                print('cannot find %s in index' % pre)
                continue

            col = index[pre]
            cur = [af]

            for row in range(1, len(stateList)):
                if post not in index:  # in stateDict[pre]:
                    cur.append(str(post == stateList[row][col]))
                else:
                    if post in index:
                        col_post = index[post]
                        if stateList[row][col] != 'Undefined' and stateList[row][col_post] != 'Undefined':
                            cur.append(str(stateList[row][col_post] == stateList[row][col]))
                        else:
                            cur.append('Undefined')
                    else:
                        cur = []
                        break
            if cur:
                new_statelist.append(cur)
                new_stateDict[af] = {x for x in cur} - {af}

        t_statelist = list(list(i) for i in zip(*new_statelist))
        assert len(new_statelist) == len(t_statelist[0])
        assert len(new_statelist[0]) == len(t_statelist)

        with open('{0}/trans_dataset.csv'.format(self.name), 'w') as f:
            for state_line in t_statelist:
                f.write('{}\n'.format(','.join(state_line)))

        print("Features / Atomic predicates: % d " % len(atom_feature))
        return t_statelist, new_stateDict

    def states2num_atom(self, statesDict):
        newDict = collections.defaultdict(lambda: collections.defaultdict(int))
        itemMeaning = {}
        cnt = 0

        for key, value in statesDict.items():
            for v in value:
                if v == 'Undefined':
                    continue
                low_key = key.lower()
                if 'true' in low_key or 'false' in low_key:
                    if 'true' in low_key:
                        itemMeaning[cnt] = key if v.lower() == 'true' else re.sub('true', 'false', key)
                    else:
                        itemMeaning[cnt] = key if v.lower() == 'true' else re.sub('false', 'true', key)
                else:
                    if v.lower() == 'false':
                        itemMeaning[cnt] = re.sub(r'=', '!=', key)
                    else:
                        itemMeaning[cnt] = key

                newDict[key][v] = cnt
                cnt += 1
        # print('ItemMeaning:', itemMeaning)
        # for key, value in itemMeaning.items():
        #     print(key, value)
        print('Total products in rs: %d ' % len(itemMeaning))
        return newDict, itemMeaning

    def states2num(self, statesDict):
        newDict = collections.defaultdict(lambda: collections.defaultdict(int))
        itemMeaning = {}
        cnt = 0

        for key, value in statesDict.items():
            for v in value:
                if v == 'Undefined':
                    continue
                if '!' in v:
                    itemMeaning[cnt] = key + ' != ' + v[1:]
                else:
                    itemMeaning[cnt] = key + ' = ' + v
                newDict[key][v] = cnt
                cnt += 1

        print('\nTotal products in rs: %d \n---------------------------' % len(itemMeaning))

        return newDict, itemMeaning

    def mapStates(self, mappingDict, stateList):
        print('Mapping states into numbers using all variables...')
        states_numberful = []
        for r in range(1, len(stateList)):
            temp = set()
            for c in range(len(stateList[0])):
                if stateList[r][c] != 'Undefined':
                    temp.add(mappingDict[stateList[0][c]][stateList[r][c]])
            states_numberful.append(temp)

        print('successfully mapped!')
        return states_numberful

    def get_atoms(self):
        file_name = "{}/atom.txt".format(self.name)
        return set(filter(lambda x: x,
                          map(lambda x: re.sub(r'[()]', '', x.strip()), open(file_name, 'r').read().split("\n"))))

    def select_global(self, itemMeaning):
        global_vars = set()
        for k, v in itemMeaning.items():
            if not re.search('[\[\]]', v):
                global_vars.add(k)
        return global_vars

    def negative(self, stateList, statesDict):
        for i in range(1, len(stateList)):
            n = len(stateList[i])
            for j in range(n):
                vals = statesDict[stateList[0][j]]
                if len(vals) <= 2:
                    continue
                for v in vals:
                    if i == 1:
                        stateList[0].append(stateList[0][j])
                    stateList[i].append(v if v == stateList[i][j] else '!' + v)

        statesDict2 = self.enumerateStates(stateList)
        return stateList, statesDict2


class Save_Load_Data(object):
    def __init__(self, protocol_name):
        self.L_name = protocol_name + '/backup/' + 'L_' + protocol_name + '.pkl'
        self.Support_name = protocol_name + '/backup/' + 'SupportData_' + protocol_name + '.pkl'

        if not os.path.exists(protocol_name + '/backup'):
            os.mkdir(protocol_name + '/backup')

    def load_from_plk(self):
        print("Loading L and Supportive Data ........")
        L = joblib.load(self.L_name)
        support_data = joblib.load(self.Support_name)
        print("L and Supportive Data loaded successfully!")
        return L, support_data

    def save_to_plk(self, L, support_data):
        print("Saving L and Supportive data......")
        joblib.dump(L, self.L_name)
        joblib.dump(support_data, self.Support_name)
        print("L and Supportive data saved Successfully!")


class RuleLearing(object):
    def __init__(self, protocol_name, dataset, itemMeaning, global_vars=set(), max_freq_size=3, min_support=0.0,
                 min_confidence=1.0):

        self.protocol_name = protocol_name
        self.dataset = dataset
        self.global_vars = global_vars
        self.itemMeaning = itemMeaning
        self.max_freq_size = max_freq_size
        self.min_support = min_support
        self.min_confidence = min_confidence
        self.d_super_set = collections.defaultdict(set)

    def execute(self):
        L, support_data = self.apriori(self.global_vars)
        bigRuleList = self.generateRules(L, support_data)
        rule_tuple, rule_string_list = self.prntRules(bigRuleList)
        return rule_tuple, rule_string_list

    def symmetry_reduction(self, rule_tuple, rule_string_list, all_types):
        print('Symmetry reducing rules...')

        min_rule_tuple, min_rule_string_list = [], []
        for (pre, cond), rule_string in zip(rule_tuple, rule_string_list):
            pre_var_set = set(map(lambda x: x.split(' ')[0], pre))
            cond_var = cond.split(' ')[0]
            if cond_var not in pre_var_set:
                min_rule_tuple.append((pre, cond))
                min_rule_string_list.append(rule_string)
        print('Remove redundant: before : {}, after: {}'.format(len(rule_tuple), len(min_rule_tuple)))

        rule_string_set = set(min_rule_string_list)

        for rule_string in min_rule_string_list:
            for t in all_types:
                tmp_stmt = rule_string
                cur_t_set = set(re.findall('%s_\d' % t, rule_string))
                if len(cur_t_set) == 0:  # not contain type parameter
                    continue
                elif len(cur_t_set) == 1:  # 含一种type parameter, such as 'NODE_1'
                    if '%s_1' % t in tmp_stmt:
                        tmp_stmt = re.sub('%s_1' % t, '%s_2' % t, rule_string)
                    elif '%s_2' % t in tmp_stmt:
                        tmp_stmt = re.sub('%s_2' % t, '%s_1' % t, tmp_stmt)
                    else:
                        print('Too many parameters!')
                    if tmp_stmt in rule_string_set:
                        # print('here')
                        # print(tmp_stmt, rule_string, tmp_stmt in rule_string_set, rule_string in rule_string_set)
                        if rule_string in rule_string_set:
                            rule_string_set.remove(rule_string)
                elif len(cur_t_set) == 2:  # 含2种type parameter, such as 'NODE_1' and 'NODE_2'
                    cur_t_dict = {}
                    for i, cur_t in enumerate(cur_t_set):
                        cur_t_dict['REP_X_%d' % i] = cur_t
                        tmp_stmt = re.sub(cur_t, 'REP_X_%d' % i, tmp_stmt)
                    for k, v in cur_t_dict.items():
                        tmp_stmt = re.sub(k, (cur_t_set - set([v])).pop(), tmp_stmt)
                    if tmp_stmt in rule_string_set:
                        if rule_string in rule_string_set:
                            rule_string_set.remove(rule_string)
                else:
                    print('Too many types of parameters!')

        sym_red_rule_string = list(rule_string_set)
        sym_red_rule_tuple = list(map(lambda x: split_string_to_tuple(x), sym_red_rule_string))
        assert len(sym_red_rule_string) == len(sym_red_rule_tuple)

        print('Reduction result: before : {}, after: {}'.format(len(min_rule_tuple), len(sym_red_rule_tuple)))
        return sym_red_rule_tuple, sym_red_rule_string

    def instantiate(self, rule_tuple, rule_string_list, all_types):
        print('Instantiating rules...')
        fout = '%s/aux_invs.txt' % self.protocol_name

        rule_string_set = set(rule_string_list)

        # print(rule_string_list)
        for rule_string in rule_string_list:
            for t in all_types:
                tmp_stmt = rule_string
                cur_t_set = set(re.findall('%s\_\d' % t, rule_string))
                if len(cur_t_set) == 0:  # not contain type parameter
                    continue
                elif len(cur_t_set) == 1:  # 含一种type parameter, such as 'NODE_1'
                    if '%s_1' % t in tmp_stmt:
                        tmp_stmt = re.sub('%s_1' % t, '%s_2' % t, rule_string)
                    elif '%s_2' % t in tmp_stmt:
                        tmp_stmt = re.sub('%s_2' % t, '%s_1' % t, tmp_stmt)
                    else:
                        print('Too many parameters!')
                    if tmp_stmt not in rule_string_set:
                        rule_string_set.add(tmp_stmt)
                elif len(cur_t_set) == 2:  # 含2种type parameter, such as 'NODE_1' and 'NODE_2'
                    cur_t_dict = {}
                    for i, cur_t in enumerate(cur_t_set):
                        cur_t_dict['REP_X_%d' % i] = cur_t
                        tmp_stmt = re.sub(cur_t, 'REP_X_%d' % i, tmp_stmt)
                    for k, v in cur_t_dict.items():
                        tmp_stmt = re.sub(k, (cur_t_set - set([v])).pop(), tmp_stmt)
                    if tmp_stmt not in rule_string_set:
                        rule_string_set.add(tmp_stmt)
                else:
                    print('Too many types of parameters!')

        sym_expan_rule_string = list(rule_string_set)
        sym_expan_rule_tuple = list(map(lambda x: split_string_to_tuple(x), sym_expan_rule_string))
        assert len(sym_expan_rule_string) == len(sym_expan_rule_tuple)
        print('Expansion result: before : {}, after: {}'.format(len(rule_tuple), len(sym_expan_rule_tuple)))

        with open(fout, 'w') as f:
            for cnt, stmt in enumerate(sorted(sym_expan_rule_string, key=lambda x: len(x)), 1):
                f.write('rule_%d: %s\n' % (cnt, stmt))

        return sym_expan_rule_tuple, sym_expan_rule_string

    # def check_sym(self, all_types, rule_tuple):
    #     print('Checking symmetry rules..')
    #
    #     sortedRuleTuple = sorted(rule_tuple, key=lambda x: len(x[0]), reverse=True)
    #     without_type, with_type_1, with_type_2 = [], [], []
    #     rest_rule_tuple, rule_need_test = [], []
    #     # classify rules
    #     for pre, cond in sortedRuleTuple:
    #         for t in all_types:
    #             if len(list(filter(lambda x: re.findall(r'%s\_\d' % t, x), pre))) == 0 and not re.findall(r'%s\_\d' % t,
    #                                                                                                       cond):
    #                 without_type.append((pre, cond))
    #             elif len(pre) == 1:
    #                 with_type_1.append((pre, cond))
    #             elif len(pre) == 2:
    #                 with_type_2.append((pre, cond))
    #
    #     print('Rule without type parameters: %d\nRule with parameters: %d' % (
    #         len(without_type), len(with_type_1) + len(with_type_2)))
    #
    #     for pre, cond in with_type_1:
    #         stmt = list(pre)
    #         stmt.append(cond)
    #         stmt = ','.join(sorted(stmt))
    #         for t in all_types:
    #             tmp_stmt = stmt
    #             if '%s_1' % t in tmp_stmt:
    #                 tmp_stmt = re.sub('%s_1' % t, '%s_2' % t, tmp_stmt)
    #                 tmp_stmt_split = split_back(tmp_stmt)
    #                 if tmp_stmt_split in with_type_1:
    #                     rest_rule_tuple.append(tmp_stmt_split)
    #                 else:
    #                     rule_need_test.append(tmp_stmt)
    #             if '%s_2' % t in tmp_stmt:
    #                 tmp_stmt = re.sub(r'%s_2' % t, '%s_1' % t, tmp_stmt)
    #                 tmp_stmt_split = split_back(tmp_stmt)
    #                 if tmp_stmt_split in with_type_1:
    #                     rest_rule_tuple.append(tmp_stmt_split)
    #                 else:
    #                     rule_need_test.append(tmp_stmt)
    #
    #     for pre, cond in with_type_2:
    #         stmt = list(pre)
    #         stmt.append(cond)
    #         stmt = ','.join(sorted(stmt))
    #         for t in all_types:
    #             tmp_stmt = stmt
    #             if '%s\_1' % t in tmp_stmt:
    #                 tmp_stmt = re.sub(r'%s\_1' % t, '%s_2' % t, tmp_stmt)
    #                 tmp_stmt_split = split_back(tmp_stmt)
    #                 if tmp_stmt_split in with_type_2:
    #                     rest_rule_tuple.append(tmp_stmt_split)
    #             if '%s\_2' % t in tmp_stmt:
    #                 tmp_stmt = re.sub(r'%s\_2' % t, '%s_1' % t, tmp_stmt)
    #                 tmp_stmt_split = split_back(tmp_stmt)
    #                 if tmp_stmt_split in with_type_2:
    #                     rest_rule_tuple.append(tmp_stmt_split)
    #
    #     rest_rule_tuple.extend(without_type)
    #
    #     return rest_rule_tuple

    def minimize_rule(self, rest_rule_tuple):
        print('Minimizing rules..')
        fout = '%s/min_rule.txt' % self.protocol_name
        rest_rule_tuple = sorted(rest_rule_tuple, key=lambda x: len(x[0]))
        # rules = list(map(lambda line: line.split(' -> '), sorted(rest_rule_tuple, key=lambda x: len(x))))
        # print('min rules % d' % len(rules))
        # joblib.dump(rules, '%s/data/min_asso.pkl' % self.protocol_name)
        # rules = joblib.load('mutualEx/data/min_asso.pkl')

        left, right = [], []
        for pre, cond in rest_rule_tuple:
            left.append(list(pre))
            right.append(cond)

        same_right = collections.defaultdict(list)
        for l, r in zip(left, right):
            same_right[r].append(l)

        for r, left_list in same_right.items():
            index = [x for x in range(len(left_list))]
            for i in range(len(left_list)):
                for j in range(i + 1, len(left_list)):
                    if j not in index: continue
                    if not (set(left_list[i]) - set(left_list[j])):
                        index.remove(j)
            same_right[r] = [left_list[i] for i in index]

        min_rule_string, min_rule_tuple = [], []

        for r, left_list in same_right.items():
            for l in left_list:
                # if left part doesn't contain array variable, then continue
                if not re.search('[\[\]]', ''.join(l)):
                    continue
                min_rule_tuple.append((set(l), r))
                min_rule_string.append('{} -> {}'.format(' & '.join(l), r))

        with open(fout, 'w') as f:
            for cnt, stmt in enumerate(min_rule_string, 1):
                f.write('rule_%d: %s\n' % (cnt, stmt))

        print('Before: {}, After: {}'.format(len(rest_rule_tuple), len(min_rule_tuple)))
        return min_rule_tuple, min_rule_string

    def createC1(self, dataSet):  # creat candidates frequent set with 1 element
        C1 = []
        for transaction in dataSet:
            for item in transaction:
                if [item] not in C1:
                    C1.append([item])

        C1.sort()
        return list(map(frozenset, C1))  # use frozen set so we can use it as a key in a dict

    def scanD(self, D, Ck, minSupport):
        print("len d: {}, len ck:{} ".format(len(D), len(Ck)))
        print("time complexity will be: O({})".format(len(D) * len(Ck)))

        ssCnt = {}
        for key in Ck:
            can = list(key)
            res = self.d_super_set[can[0]]
            for t in can[1:]:
                res = res & self.d_super_set[t]
            if len(res) != 0:
                ssCnt[key] = len(res)

        numItems = float(len(D))
        retList = []
        supportData = {}
        for key in ssCnt:
            support = ssCnt[key] / numItems
            if support >= minSupport:
                retList.append(key)
            supportData[key] = support
        return retList, supportData

    def _build_trie(self, data, k):
        root = {}
        for i, row in enumerate(data):
            row = sorted(list(row))[:k - 2]
            cur = root
            for d in row:
                if d not in cur:
                    cur[d] = {}
                cur = cur[d]
            cur[i] = None
        return root

    def aprioriGen(self, Lk, k):  # creates Ck
        retList = []
        root = self._build_trie(Lk, k)
        for i, row in enumerate(Lk):
            row = sorted(list(row))[:k - 2]
            cur = root
            ok = True
            for d in row:
                if d not in cur:
                    ok = False
                    break
                cur = cur[d]
            if ok:
                retList.extend([Lk[i] | Lk[j] for j in cur.keys() if i < j])
        return retList

    def _build_super_set(self, data: list):
        """
        :param data: [set,set..]
        :return:
        """
        print('---build_super_set----')
        for i, d in enumerate(data):
            for x in d:
                self.d_super_set[x].add(i)

        print('build_super_set done')

    def apriori(self, global_vars):
        print('--------------------------\nGenerating frequent set........')
        start_freq = time.time()
        C1 = self.createC1(self.dataset)
        D = list(map(set, self.dataset))  # add cast to list. In py3, map create a genarator.

        self._build_super_set(D)

        start = time.time()
        L1, supportData = self.scanD(D, C1, self.min_support)
        print('time for scan L1: %.3f' % (time.time() - start))

        L = [L1]
        k = 2
        while k <= self.max_freq_size:
            Ck = self.aprioriGen(L[k - 2], k)
            start = time.time()

            # remove those 3 global variables if minimize = True
            Ck = filter(lambda x: len(x & global_vars) < 3, Ck)  # if is_minimize else Ck

            all_lemma_set = list(Ck)
            Lk, supK = [], {}

            for t in [self.parellel_cal(D, all_lemma_set, self.min_support)]:
                Lk.extend(t[0])
                supK.update(t[1])

            print('time for scan L%d : %.3f\n-------------------\n' % (k, time.time() - start))

            supportData.update(supK)
            L.append(Lk)
            k += 1

        print('Running time for frequent sets: %.3f s' % (time.time() - start_freq))
        return L, supportData

    def parellel_cal(self, D, Ck, minSupport):
        Lk, supK = self.scanD(D, Ck, minSupport)  # scan DB to get Lk
        return (Lk, supK)

    def generateRules(self, L, supportData, minConf=1.0):  # supportData is a dict coming from scanD
        start = time.time()

        bigRuleList = []
        for i in range(1, len(L)):  # only get the sets with two or more items
            for freqSet in L[i]:
                H1 = [frozenset([item]) for item in freqSet]
                if i > 1:
                    self.rulesFromConseq(freqSet, H1, supportData, bigRuleList, minConf)
                else:
                    self.calcConf(freqSet, H1, supportData, bigRuleList, minConf)

        print('Running time for calculating association rules: %.3f s ' % (time.time() - start))

        return bigRuleList

    def calcConf(self, freqSet, H, supportData, brl, minConf=1.0):
        prunedH = []  # create new list to return

        for cond in H:
            conf = supportData[freqSet] / supportData[cond]  # calc confidence
            if conf >= minConf:
                if len(freqSet - cond) == 1:
                    brl.append((cond, freqSet - cond, conf))
                prunedH.append(cond)

        return prunedH

    def rulesFromConseq(self, freqSet, H, supportData, brl, minConf=1.0):
        m = len(H[0])
        if (len(freqSet) > (m + 1)):  # try further merging
            Hmp1 = self.aprioriGen(H, m + 1)  # create Hm+1 new candidates

            Hmp1 = self.calcConf(freqSet, Hmp1, supportData, brl, minConf)

            if (len(Hmp1) > 1):  # need at least two sets to merge
                self.rulesFromConseq(freqSet, Hmp1, supportData, brl, minConf)

    def prntRules(self, bigRuleList):
        # sortedRuleList = sorted(bigRuleList, key=lambda d: d[2], reverse=True)
        print('\n\nAssociation rules: {}'.format(len(bigRuleList)))

        ar_filename = '%s/assoRules.txt' % self.protocol_name
        rule_tuple, rule_string_list = [], []

        for ruleTup in bigRuleList:
            ant, conseq = ruleTup[0], ruleTup[1]
            e_ant = set(self.itemMeaning[a] for a in ant)
            e_conseq = list(self.itemMeaning[c] for c in conseq)
            rule_tuple.append((e_ant, e_conseq[0]))
            rule_string_list.append(' & '.join(e_ant) + ' -> ' + ''.join(e_conseq))

        with open(ar_filename, 'w') as fw:
            for i, rule in enumerate(sorted(rule_string_list, key=lambda x: len(x)), 1):
                fw.write('rule_%d: %s\n' % (i, rule))

        return rule_tuple, rule_string_list

    # def para_rules(self, para_digit, save=True):
    #     """
    #     parameterize association rules:
    #     1. parameterize: paralized line, subsitute parameters into P1,P2,... in original order
    #         i.e., n[NODE_1] = NODE_2 --> n[P1] = P2
    #               n[NODE_2] = NODE_1 --> n[P1] = P2
    #
    #     2. remove repeated: predicates that before and after '->' have the same variable name
    #         v1 = e1 -> v1 != e2
    #         or
    #         v1 = e1 & v2 = e3 -> v1 != e2
    #        will be removed
    #     """
    #
    #     left, right = [], []
    #     para_rules, rules = set(), set()
    #
    #     def paralize(line, par):
    #         """
    #         paralized line, subsitute parameters into P1,P2,... in original order
    #         i.e., n[NODE_1] = NODE_2 --> n[P1] = P2
    #               n[NODE_2] = NODE_1 --> n[P1] = P2
    #         :param line:
    #         :param par:
    #         :return: paralized line, without changing the original parameters such as 'NODE_1', 'NODE_2'
    #         """
    #
    #         search_para = re.search(r'\[\d\]', line) if para_digit else re.search(r'\[%s\_\d\]' % par, line)
    #
    #         cnt = 1
    #         while search_para:
    #             para_code = self.para_map[par]
    #             line = line.replace(search_para.group(), '[%s%d]' % (para_code, cnt))
    #             search_para = re.search(r'\[\d\]', line) if para_digit else re.search(r'\[%s\_\d\]' % par, line)
    #             cnt += 1
    #         return line
    #
    #     for ant, conse in zip(self.antecedants, self.consequents):
    #         # if len(conse) <= 1:
    #         line = "{} -> {}".format(' & '.join(sorted(ant)), conse)
    #         for par in self.params:
    #             paralized_line = paralize(line, par)
    #             # paralized_line = line
    #             if paralized_line in para_rules:
    #                 # para_rules.remove(paralized_line)
    #                 continue
    #             else:
    #                 para_rules.add(paralized_line)
    #
    #                 # extract variable names and remove the rule which has same variable in both sides of '='
    #                 left_var, right_var = set([a.split(' ')[0] for a in ant]), set([conse.split(' ')[0]])
    #
    #                 if left_var.issubset(right_var) or right_var.issubset(
    #                         left_var):  # or not re.search('[\[\]]', ''.join(left_var)):
    #                     para_rules.remove(paralized_line)
    #                     continue
    #                 else:
    #                     left.append(sorted([a for a in ant]))
    #                     right.append(conse)
    #                     rules.add("{} -> {}".format(' & '.join(sorted(ant)), conse))
    #
    #     assert (len(left) == len(right))
    #
    #     print('Parametrized rules: %d ' % len(left))
    #
    #     with open('%s/assoRule_min.txt' % self.name, 'w') as fw:
    #         for i, pr in enumerate(para_rules, 1):
    #             fw.write('rule_%d: %s\n' % (i, pr))
    #             print('rule_%d: %s\n' % (i, pr))
    #
    #     if save:
    #         f_left = '%s/data/left.pkl' % self.name
    #         f_right = '%s/data/right.pkl' % self.name
    #
    #         joblib.dump(left, f_left)
    #         joblib.dump(right, f_right)
    #
    #     return para_rules

    # def instantiate(self, para_line, paras=['NODE_1', 'NODE_2']):
    #     """
    #     instantiate association rules.
    #     E.g. n[P1] -> P2  will be instantiated into :
    #          n[i] -> j
    #     and  n[j] -> i
    #     :param para_line:
    #     :return:
    #     """
    #     # paras = ['NODE_1', 'NODE_2']
    #     fname = '{0}/aux_invs.txt'.format(self.name)
    #     ins_lines = []
    #     left, right = [], []
    #     for line in para_line:
    #         for index in range(len(paras)):
    #             temp = line
    #             for par in self.params:
    #                 para_code = self.para_map[par]
    #                 search_para = re.search(r'%s\d' % para_code, temp)
    #
    #                 while search_para:
    #                     temp = re.sub(search_para.group(), paras[index], temp)
    #                     search_para = re.search(r'%s\d' % para_code, temp)
    #                     index ^= 1
    #                 ins_lines.append(temp)
    #                 left.append([a for a in sorted(temp.split(' -> ')[0].split(' & '))])
    #                 right.append(temp.split(' -> ')[1])
    #
    #     with open(fname, 'w') as f:
    #         for cnt, line in enumerate(ins_lines, 1):
    #             f.write('rule_%d:   %s\n' % (cnt, line))
    #
    #     print('instantiated rules: %d ' % len(ins_lines))
    #     self.antecedants, self.consequents = left, right
    #     return ins_lines
    #

    #
    # def built_map(self):
    #     """
    #     build a rule map using antecendents:
    #
    #     e.g. n[NODE_1] = C -> n[NODE_2] != C
    #     build a rule map:
    #     {n[NODE]: n[NODE_1] = C -> n[NODE_2] != C}
    #
    #     :return:
    #     """
    #
    #     rules_map = collections.defaultdict(lambda: collections.defaultdict(set))
    #     par = self.params[0]
    #
    #     for left, right in zip(self.antecedants, self.consequents):
    #         # key = ','.join(sorted(left))
    #         # for par in self.params:
    #         #     key = lambda x : re.sub(r'%s\_\d' % par, par, x)
    #
    #         key = frozenset(map(lambda x: re.sub(r'%s\_\d' % par, par, x), left))
    #         # key = frozenset(map(lambda x: re.sub(r'\d', par, x), left))
    #
    #         rules_map[key][frozenset(left)].add(right)
    #     return rules_map

    def slct_rules_by_guards(self, rules_map, guards, par, save=True, load=False):
        if load and os.path.exists("{}/data/norm_rule_dict.pkl".format(self.name)) and os.path.exists(
                "{}/data/rules.pkl".format(self.name)):
            return joblib.load("{}/data/norm_rule_dict.pkl".format(self.name)), joblib.load(
                "{}/data/rules.pkl".format(self.name))

        par = par[0]
        if guards:
            norm_rule_dict = {key: rules for key, rules in rules_map.items() if set(key).issubset(guards)}
        else:
            norm_rule_dict = {key: rules for key, rules in rules_map.items()}

        rules = set()

        for ant_dict in norm_rule_dict.values():
            for ant, conse_set in ant_dict.items():
                for conse in conse_set:
                    line = "{} -> {}".format(' & '.join(sorted(ant)), conse)
                    search_para = re.search(r'%s\_\d' % par, line)
                    # search_para = re.search(r'\d', line)

                    cnt = 1
                    while search_para:
                        line = re.sub(search_para.group(), 'P%d' % cnt, line)
                        search_para = re.search(r'%s\_\d' % par, line)
                        # search_para = re.search(r'%s\_\d' % par, line)

                        cnt += 1

                    rules.add(line)
        print('select %d association rules' % len(rules))

        # fout = '%s/selected_by_guard.txt' % self.name
        # with open(fout, 'w') as f:
        #     for i, r in enumerate(rules, 1):
        #         f.write('rule_%d: %s\n' % (i, r))

        # save data
        # self.write_to_file(rules)

        if save:
            joblib.dump(norm_rule_dict, "{}/data/norm_rule_dict.pkl".format(self.name))
            joblib.dump(rules, "{}/data/rules.pkl".format(self.name))

        return norm_rule_dict, rules


class SlctInv(object):
    def __init__(self, name, par, all_types, home=False):
        self.name = name
        self.home = home
        self.murphi_dir = self.loc_murphi_dir()
        self.par = par
        self.all_types = all_types
        self.counterex_index = []
        # self.test_rules = {'rule_%d' % i: rule for i, rule in enumerate(test_rules, 1)}

    # def update_test_rules(self, new_set):
    #     self.test_rules = {'rule_%d' % i: rule for i, rule in enumerate(new_set, 1)}

    def select_invariant(self, test_rule_string, num_core=multiprocessing.cpu_count(), original_file=None):
        print('\nchecking invariants...')
        original_file = "{0}/{0}.m".format(self.name) if original_file is None else original_file

        test_rule_string_dict = {'rule_%d' % i: rule for i, rule in enumerate(test_rule_string, 1)}
        translate_dic = self.translate_test_inv(test_rule_string_dict)

        n = len(test_rule_string)
        if n < 100:
            num_core = num_core
        else:
            num_core = min(num_core, n // 100)

        jobs = [(i * n // num_core, (i + 1) * n // num_core) for i in range(num_core)]

        print('ranges', jobs)
        spurious_index = []
        with multiprocessing.Pool(num_core) as p:
            spurious_index.extend(p.starmap(self.parallel,
                                            [(index_range, pid, translate_dic, original_file) for
                                             pid, index_range
                                             in enumerate(jobs, 1)]))

        spurious_index = list(set(k for key in spurious_index for k in key))
        self.counterex_index = spurious_index
        # print(self.counterex_index)

        print('original rule: {}, remove {}, remain {}'.format(n, len(spurious_index), n - len(spurious_index)))
        self.counterex_index = list(map(lambda x: int(''.join(re.findall('\_(\d*)', x))) - 1, self.counterex_index))
        return len(spurious_index), self.counterex_index

    def loc_murphi_dir(self):
        if not os.path.exists('murphi_url.txt'): raise FileExistsError
        return open('murphi_url.txt').read().strip()

    def run_murphi(self, file, aux_para=''):
        file = file.split('.')[0]
        process1 = subprocess.Popen("{0}/src/mu {1}.m".format(self.murphi_dir, file), shell=True,
                                    stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE)

        (stdout, stderr) = process1.communicate()
        if not re.search(r'Code generated', stdout.decode('utf-8')):
            print('here', stderr.decode('utf-8'))
            # raise ValueError

        command2 = "g++ -ggdb -o {0}.o {0}.cpp -I {1}/include -lm".format(file, self.murphi_dir)
        process2 = subprocess.Popen(command2, shell=True,
                                    stdout=subprocess.PIPE,
                                    stderr=subprocess.PIPE)
        process2.communicate()

        process = subprocess.Popen("{0}.o -k10000000 {1} -pr".format(file, aux_para), shell=True,
                                   stdout=subprocess.PIPE,
                                   stderr=subprocess.PIPE)

        (stdoutdata, stderrdata) = process.communicate()

        pattern_counter = re.compile(r'Invariant\s"(\w+).*"\sfailed')
        counter_ex = re.findall(pattern_counter, stdoutdata.decode('utf-8'))
        # 如果有反例，则记录它的下标， 并输出
        if len(counter_ex):
            print("%s failed!" % counter_ex[0])

        os.remove('%s.cpp' % file)
        os.remove('%s.o' % file)

        return counter_ex[0] if len(counter_ex) else 0

    def translate_test_inv(self, test_rule_string_dict):
        # test_invs is empty
        if not test_rule_string_dict: return []

        translate_dic = {}
        for key, rule in test_rule_string_dict.items():
            translate_dic.update(
                {key: '\n\nInvariant \"%s\"\n' % key + self.to_murphi(rule)})
        return translate_dic

    def parallel(self, index_range, id, translate_dic, original_file):
        start, end = index_range
        counters = []
        new_file = "{}_{}.m".format(original_file.split('.')[0], id)
        copyfile(original_file, new_file)
        with open(new_file, 'a') as f:
            for rule_num in range(start + 1, end + 1):
                f.writelines(translate_dic['rule_%d' % rule_num])
        counter_ex = self.run_murphi(new_file)

        while counter_ex:
            if not re.findall('rule_\d', counter_ex):
                print(counter_ex)
                break
            counters.append(counter_ex)
            pattern = re.compile(r'Invariant \"%s\".*?;\n' % counter_ex, re.S)
            new_content = re.sub(pattern, '', open(new_file).read())

            with open(new_file, 'w') as fw:
                fw.writelines(new_content)
            counter_ex = self.run_murphi(new_file)

        os.remove("{}.m".format(new_file.split('.')[0]))
        # os.remove("{}.cpp".format(new_file.split('.')[0]))
        # os.remove("{}.o".format(new_file.split('.')[0]))

        return counters

    def to_murphi(self, rule):
        """
        translate an association rule('Chan2[__P1__].Cmd = Inv -> Cache[__P2__].Data = AuxData') into murphi code
        invariant "rule_1"
            forall __P1__: NODE do forall __P2__: NODE do
            __P1__ != __P2__ -> (Chan2[__P1__].Cmd = Inv -> Cache[__P2__].Data = AuxData)
        end end;

        :param rule: an association rule
        :param par: NODE
        :return: murphi code
        """
        cur_paras_dict = {}
        for t in self.all_types:
            find_result = re.findall(r'%s\_\d' % t, rule)
            for result in find_result:
                cur_paras_dict.update({result: t})

        murphi_string = 'forall ' if cur_paras_dict else ''

        unequal_list, para_list = [], []
        for p, t in cur_paras_dict.items():
            para_list.append('{} : {} '.format(p, t))
            if self.home: unequal_list.append('Home != {}'.format(p))
        murphi_string += ('; '.join(para_list) + 'do\n\t') if cur_paras_dict else ''

        index = 1
        cur_para_list = list(cur_paras_dict.keys())
        while index < len(cur_paras_dict):
            if cur_paras_dict[cur_para_list[index - 1]] == cur_paras_dict[cur_para_list[index]]:
                unequal_list.append("{} != {}".format(cur_para_list[index - 1], cur_para_list[index]))
            index += 1

        unequal_string = '(' + ' & '.join(unequal_list) + ') ->\n\t' if unequal_list else ''
        murphi_string += unequal_string  # ('\n\t%s' % unequal_string + '\n\t->\n\t') if unequal_string else ''
        murphi_string += ("({})".format(rule))
        murphi_string += '\nend;\n' if cur_paras_dict else ';\n'

        return murphi_string

    def check_usedF(self, test_rule_string, num_core=multiprocessing.cpu_count(), original_file=None):
        original_file = "{0}/{0}.m".format(self.name) if original_file is None else original_file
        print('checking %s' % original_file)
        spurious_cnt, counterex_index = self.select_invariant(test_rule_string, num_core, original_file)
        print('counterex_index', counterex_index)
        if not spurious_cnt:
            print('usedF all passed!')
        else:
            print('usedF failed.')
            print(spurious_cnt)

        return counterex_index

    # def prnt_inv(self):
    #     invs = set(v for k, v in self.test_rules.items())
    #     with open("{}/invs.txt".format(self.name), 'w') as f:
    #         for i, inv in enumerate(invs, 1):
    #             f.writelines("rule_%d: %s\n" % (i, inv))
    #     return invs

#
# protocol_name = "mutualEx"
# fileaname = "mutdata.m"
#
# replace_index = None  # if NUM == 2 else {'NODE_1': 'Home'}
# processor = DataProcess(protocol_name, replace_index=replace_index)
# dataset, itemMeaning, para_digit = processor.execute(load=False)
# global_vars = processor.select_global(itemMeaning)
# print('local', global_vars)
#
# learner = RuleLearing(protocol_name, dataset, itemMeaning)
# rule_tuple, rule_string_list = learner.execute()
# all_types = ['NODE']
# # learner.check_sym(all_types, rule_tuple)
# rule_tuple, rule_string_list = learner.symmetry_reduction(rule_tuple, rule_string_list, all_types)
# # print(len(rule_tuple), len(rule_string_list))
#
# # test_rule = ['n[NODE_2] = C & n[NODE_1] = I -> x = true', 'n[NODE_2] = C & n[NODE_1] = I -> x = false']
# selector = SlctInv(protocol_name, [], all_types, rule_string_list, home=False)
# _, counterex_index = selector.select_invariant(1, '{0}/{0}.m'.format(protocol_name))
#
# tmp_tuple, tmp_string = copy.deepcopy(rule_tuple), copy.deepcopy(rule_string_list)
# for cex in counterex_index:
#     tmp_tuple.remove(rule_tuple[cex])
#     tmp_string.remove(rule_string_list[cex])
#
# rule_tuple, rule_string_list = tmp_tuple, tmp_string
#
# # learner.minimize_rule(all_types, rule_tuple)
# min_rule_tuple, min_rule_string = learner.minimize_rule(rule_tuple)
# aux_inv, aux_inv_string = learner.instantiate(min_rule_tuple, min_rule_string, all_types)
