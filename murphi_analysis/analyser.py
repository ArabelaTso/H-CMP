import re
import sys
import copy
import getopt
from preprocess_opts.utils import transform

from shutil import copyfile
import collections


class TypeDef(object):
    """
    Deal with type and const in murphi

    It can deal with the following definition:
        const
            NODE_NUM : 3;
            DATA_NUM : 2;
        type
            NODE : scalarset(NODE_NUM);
            DATA : 1..DATA_NUM;

    and turn it into:
        self.type = {NODE:NODE_NUM, DATA: DATA_NUM}
        self.const = {NODE_NUM : 3, DATA_NUM:2}
        para = ["NODE"] -- because the type used to represent 'processor' is usually used with 'array [__] of'
    """

    def __init__(self, text):
        self.text = text
        self.type = {}
        self.const = {}
        self.para = []
        self.enumvalues = set()
        self.evaluate()

    def evaluate(self):
        self.eval_scalarset()
        self.eval_const()
        self.eval_arr()
        self.evalEnum()
        # print(self.type, self.const, self.para, self.enumvalues)

    def evalEnum(self):
        enums = re.findall(r'(\w*?)\s*:\s*enum\s*\{(.*?)\}\s*;', self.text, re.S)
        for _, vstr in enums:
            values = list(filter(lambda x: x, list(map(lambda y: y.strip(), vstr.split(',')))))
            for v in values:
                self.enumvalues.add(v)

    def eval_scalarset(self):
        """
        collect types from two kinds of type:
            1. NODE: 1..NODE_NUM
            2. NODE: scalarset(NODE_NUM)

        :param text: murphi description
        :return: NONE
        """
        scalarsets = re.findall(r'(\w*?)\s*:\s*\w+?\s*\.\.\s*(\w+?)\s*;', self.text, re.S)
        scalarsets2 = re.findall(r'(\w*?)\s*:\s*scalarset\((\w+)\)', self.text, re.S)

        self.type.update({name: num for name, num in scalarsets})
        self.type.update({name: num for name, num in scalarsets2})

    def eval_arr(self):
        """
        For now, the type that will be used as a represent of a processor usually can be found in form of :
        array [NODE] of ...
        So identifying it using 'array [\w+] of', and check whether it is in self.types.
        :return:
        """
        pattern = re.compile(r'array\s*\[\s?(\w+)\s?\]\s*of\s*.+')
        array = list(set(re.findall(pattern, self.text)))
        self.para = [a for a in array if a in self.type]

    def eval_const(self):
        config = re.findall(r'(\w+)\s*:\s*(\d+)\s*;', self.text)
        self.const = {v: d for v, d in config}

    def reset_const(self, para, num):
        """
        reset the configuration by the given parameter name and new number
        :param para:
        :param num:
        :return: new murphi description
        """
        para_const = self.type[para]
        self.text = re.sub(r'%s\s?:\s?(\d+?)\s?;' % para_const, r"%s : %d;" % (para_const, num), self.text)
        return self.text


class Field(object):
    def __init__(self):
        self.para_dict = {}
        self.content = []


def normalization(obj):
    """
    normalize guard_obj or action_obj
    :param obj: {i:TYPE_NODE} [n[i].state = invalid]  normalize -->  n[TYPE_NODE_1].state = invalid
    :return: None
    """
    dic = obj.mainfield.para_dict.copy()
    for item in obj.forfield: dic.update(item.para_dict)
    for item in obj.existfield: dic.update(item.para_dict)

    global_dic = number_type(dic)
    obj.normal_guards = norm_rep(global_dic, obj.all_sentence)

    main_dic = number_type(obj.mainfield.para_dict)
    obj.mainfield.content = norm_rep(main_dic, obj.mainfield.content)

    for index in range(len(obj.forfield)):
        obj.forfield[index].para_dict.update(obj.mainfield.para_dict)
        # temp_dic.update(obj.mainfield.para_dict)
        # for_dic = number_type(temp_dic)
        obj.forfield[index].content = norm_rep(global_dic, obj.forfield[index].content)
        print(global_dic, obj.forfield[index].para_dict)
        obj.forfield[index].para_dict = pair_2_dict(global_dic, obj.forfield[index].para_dict)

    for index in range(len(obj.existfield)):
        obj.existfield[index].para_dict.update(obj.mainfield.para_dict)
        # temp_dic.update(obj.mainfield.para_dict)
        # exist_dic = number_type(temp_dic)
        obj.existfield[index].content = norm_rep(global_dic, obj.existfield[index].content)
        obj.existfield[index].para_dict = pair_2_dict(global_dic, obj.existfield[index].para_dict)

    # change para_dict: {'i':'NODE}  -> {'NODE_1', 'NODE'}
    obj.mainfield.para_dict = pair_2_dict(global_dic, obj.mainfield.para_dict)


def pair_2_dict(key_dict, value_dict):
    # assert len(key_dict) == len(value_dict)
    new_dict = {}
    # for k, v in zip(key_dict.values(), value_dict.values()):
    for k in value_dict.keys():
        new_dict[key_dict[k]] = value_dict[k]
    return new_dict


def norm_rep(rep_dict, lst):
    norm_lst = []
    for item in lst:
        for p, t in rep_dict.items():
            item = re.sub(r'\b%s\b' % p, t, item)
        norm_lst.append(item)
    return norm_lst


def number_type(origin_dict):
    new_dic, type_count = {}, {}
    for p, t in origin_dict.items():
        if t not in type_count:
            type_count[t] = 1
        else:
            type_count[t] += 1
        new_dic[p] = '%s_%d' % (t, type_count[t])
    return new_dic


class Part(object):
    def __init__(self):
        self.all_sentence = set()
        self.normal_guards = set()
        self.mainfield = Field()
        self.mainfield.para_dict = {}
        self.forfield = []
        self.existfield = []

    def print_value(self, title=""):
        print('\n[%spart]' % title)
        print('- main field: \n\t- parameters: %s\n\t- content:%s' % (self.mainfield.para_dict, self.mainfield.content))
        for item in self.forfield:
            print('- forfield: \n\t- parameters: %s\n\t- content:%s' % (item.para_dict, item.content))
        for item in self.existfield:
            print('- existfield: \n\t- parameters: %s\n\t- content:%s' % (item.para_dict, item.content))


class Guard(object):
    def __init__(self, text, param_name_dict):
        self.param_name_dict = param_name_dict
        self.text = text
        self.all_sentence = set()
        self.normal_guards = set()
        self.mainfield = Field()
        self.mainfield.para_dict = param_name_dict
        self.forfield = []
        self.existfield = []
        # self.sparse()

    def sparse(self):
        def para_repl(match):
            return self.param_name_dict[match.group()] if match.group() in self.param_name_dict else match.group()

        split_guard = list(map(lambda x: x.strip(), self.text.split('&')))
        for g in split_guard:
            if g.startswith(('forall', '!forall')):
                self.deal_forall(g)
            elif g.startswith(('exists', '!exists')):
                self.deal_exist(g)
            else:
                # self.guards.add(re.sub('\w+', para_repl, g))
                self.all_sentence.add(g)
                self.mainfield.content.append(g)

    def deal_forall(self, text):
        pattern = re.compile(r'forall(.*?)do(.*)end', re.S)
        try:
            params, content = re.findall(pattern, text)[0]
        except:
            print('cannot deal with %s ' % text)
        else:
            temp_field = Field()

            param_name_dict = analyzeParams(params)
            temp_field.para_dict = param_name_dict
            # for var, type in param_name_dict.items():
            # parts = set(filter(lambda x: x, map(lambda x: re.sub('%s' % var, type, x.strip()),
            #                 filter(lambda x: len(x) > 2, re.split(r'(\||->|\n|\(|\)|&)', content)))))
            parts = set(filter(lambda x: x, map(lambda x: x.strip(),
                                                filter(lambda x: len(x) > 2,
                                                       re.split(r'&', content)))))
            # re.split(r'(\||->|\n|\(|\)|&)', content)))))

            temp_field.content = list(filter(lambda x: x, map(lambda x: x.strip(),
                                                              filter(lambda x: len(x) > 2,
                                                                     re.split(r'&', content)))))
            # re.split(r'(\||->|\n|\(|\)|&)', content)))))
            self.all_sentence |= parts
            self.forfield.append(temp_field)

    def deal_exist(self, text):
        pattern = re.compile(r'!?exists(.*?)do(.*)end', re.S)
        try:
            params, content = re.findall(pattern, text)[0]
        except:
            print('cannot deal with %s ' % text)

        temp_field = Field()

        param_name_dict = analyzeParams(params)
        temp_field.para_dict = param_name_dict
        for var, type in param_name_dict.items():
            # for var, type, statesment in forall_parts:
            parts = set(map(lambda x: re.sub(var, type, x.strip()),
                            filter(lambda x: len(x) > 2,
                                   re.split(r'&', content))))  # re.split(r'(\||->|\n|\(|\)|&)', content))))
            temp_field.content = list(map(lambda x: x.strip(),
                                          filter(lambda x: len(x) > 2, re.split(r'&',
                                                                                content))))  # re.split(r'(\||->|\n|\(|\)|&)', content))))
            self.all_sentence |= parts
            self.existfield.append(temp_field)

    def evaluate(self):
        # print('guards here:%s' % self.all_sentence)
        print('\n[Guard part]')
        print('- main field: \n\t- parameters: %s\n\t- content:%s' % (self.mainfield.para_dict, self.mainfield.content))
        for item in self.forfield:
            print('- forfield: \n\t- parameters: %s\n\t- content:%s' % (item.para_dict, item.content))
        for item in self.existfield:
            print('- existfield: \n\t- parameters: %s\n\t- content:%s' % (item.para_dict, item.content))

    def collect_atoms(self):
        atoms = set()
        dic = self.mainfield.para_dict
        for item in self.forfield:
            dic.update(item.para_dict)
        for item in self.existfield:
            dic.update(item.para_dict)
        for guard in self.all_sentence:
            for k, v in dic.items():
                guard = re.sub(r'\b%s\b' % k, v, guard, re.I)
            atoms.add(guard)
        return atoms


class Action(object):
    def __init__(self, text, param_name_dict):
        self.param_name_dict = param_name_dict
        self.text = text
        self.all_sentence = set()
        self.normal_guards = set()
        self.mainfield = Field()
        self.mainfield.para_dict = param_name_dict
        self.forfield = []
        self.existfield = []
        # self.sparse()

    def sparse(self):
        def para_repl(match):
            return self.param_name_dict[match.group()] if match.group() in self.param_name_dict else match.group()

        self.rm_for()

        split_action = list(filter(lambda x: x, map(lambda x: x.strip(), self.text.split(';'))))

        for a in split_action:
            self.all_sentence.add(a)
            self.mainfield.content.append(a)

    def rm_for(self):
        for_stmt = re.findall(r'(!?for.*?do.*?endfor;)', self.text, re.S)
        for stmt in for_stmt:
            self.deal_for(stmt)
        self.text = re.sub('for(?:.|\n)*do(?:.|\n)*endfor(?:.|\n)*?;', "", self.text, re.S).strip('\n').strip(' ')

    def deal_for(self, text):
        pattern = re.compile(r'!?for(.*?)do(.*)endfor;?', re.S)
        params, content = re.findall(pattern, text)[0]

        temp_field = Field()

        param_name_dict = analyzeParams(params)
        temp_field.para_dict = param_name_dict
        # for var, type in param_name_dict.items():
        parts = set(filter(lambda x: x, map(lambda x: x.strip(),
                                            filter(lambda x: len(x) > 2,
                                                   re.split(';', content)))))
        # re.split(r'(\||->|\n|\(|\)|&|;)', content)))))

        temp_field.content = list(filter(lambda x: x, map(lambda x: x.strip(),
                                                          filter(lambda x: len(x) > 2,
                                                                 re.split(';', content)))))
        # re.split(r'(\||->|\n|\(|\)|&|;)', content)))))
        self.all_sentence |= parts
        self.forfield.append(temp_field)

    def rm_exist(self):
        exist_stmt = re.findall(r'(!?exists.*?do.*endexists.*?;)', self.text, re.S)
        for stmt in exist_stmt:
            self.deal_exist(stmt)
        self.text = re.sub(r'!?exists(.*?)do(.*)(end|endfor);', '', self.text)

    def deal_exist(self, text):
        pattern = re.compile(r'!?exists(.*?)do(.*)end', re.S)
        params, content = re.findall(pattern, text)[0]
        temp_field = Field()

        param_name_dict = analyzeParams(params)
        temp_field.para_dict = param_name_dict
        parts = set(map(lambda x: x.strip(),
                        filter(lambda x: len(x) > 2, re.split(r'(\||->|\n|\(|\)|&)', content))))
        temp_field.content = list(map(lambda x: x.strip(),
                                      filter(lambda x: len(x) > 2, re.split(r'(\||->|\n|\(|\)|&)', content))))
        self.all_sentence |= parts
        self.existfield.append(temp_field)

    def evaluate(self):
        print('\n[Action part]')
        print('- main field: \n\t- parameters: %s\n\t- content:%s' % (self.mainfield.para_dict, self.mainfield.content))
        for item in self.forfield:
            print('- forfield: \n\t- parameters: %s\n\t- content:%s' % (item.para_dict, item.content))
        for item in self.existfield:
            print('- existfield: \n\t- parameters: %s\n\t- content:%s' % (item.para_dict, item.content))


class Ruleset(object):
    def __init__(self, data_dir, protocol_name, text, type):
        self.data_dir = data_dir
        self.protocol_name = protocol_name
        self.text = text
        self.type = type
        self.guards = set()
        self.atoms = set()
        self.print_info = ""
        self.used_inv_string_set = set()

    def collect_atoms_from_ruleset(self):
        pattern = re.compile(r'ruleset(.*?)do(.*?)endruleset\s*;', re.S)
        rulesets = pattern.findall(self.text)
        for params, rules_str in rulesets:
            param_name_dict = analyzeParams(params)
            rules = re.findall(r'(rule.*?endrule;)', rules_str, re.S)
            for each_rule in rules:
                self.collect_atoms_from_rule(each_rule, param_name_dict)

    def collect_atoms_from_rule(self, rule_text, param_name_dict):
        pattern = re.compile(r'rule\s*\"(.*?)\"\s*(.*?)==>.*?begin(.*?)endrule\s*;', re.S)
        rule_name, guards, _ = pattern.findall(rule_text)[0]
        guard_obj = Guard(guards, param_name_dict)
        guard_obj.sparse()
        # if guard_obj:
        self.atoms |= guard_obj.collect_atoms()
        print('collect atoms from %s' % rule_name)

    def sparse_rulesets(self, aux_invs, abs_type, boundary_K, logfile, print_usedinvs_to_file=False):
        pattern = re.compile(r'ruleset(.*?)do(.*?)endruleset\s*;', re.S)
        rulesets = pattern.findall(self.text)

        for params, rules_str in rulesets:
            param_name_dict = analyzeParams(params)
            rules = re.findall(r'(rule.*?endrule;)', rules_str, re.S)
            for each_rule in rules:
                # split rulename, guard part, action part
                rulename, guards_obj, actions_obj = self.sparse_rule(each_rule, param_name_dict)

                print("\n\n[Rulename]: %s" % rulename)
                open(logfile, 'a').write('\n{}\nrule {}:\n'.format('*' * 20, rulename))

                normalization(guards_obj)
                normalization(actions_obj)

                # refine guard, return useful_invs
                refiner = Reiner(rulename, guards_obj, aux_invs)
                useful_invs, useful_invs_index = refiner.find_useful_invs(boundary_K=boundary_K)
                dict_inv2index = refiner.dict_inv2index
                # print("dict_inv2index = {}".format(dict_inv2index))

                # open(logfile, 'a').write(
                #     'aux_invs used for refine:[{}],\n'.format(','.join(map(lambda x: 'rule_{}'.format(x), useful_invs_index))))

                # abstract
                abstracter = Abstractor(rulename, guards_obj, actions_obj, abs_type, useful_invs, self.type, logfile,
                                        dict_inv2index)
                abstracter.abstract()
                abstracter.used_inv_string_list = list(set(abstracter.used_inv_string_list))

                self.print_info += abstracter.print_string
                self.used_inv_string_set |= set(abstracter.used_inv_string_list)

                # open(logfile, 'a').write('\n\naux_invs: [{}]'.format(
                #     ','.join(map(lambda x: 'rule_{}'.format(abstracter.dict_inv2index[x]),
                #                  abstracter.used_inv_string_list))))

                # return abstracter.used_inv_string_list, rulename
                if print_usedinvs_to_file:
                    self.write_usedinv_to_file(abstracter.used_inv_string_list, rulename)

    def write_usedinv_to_file(self, string_list, rulename):
        fout = '{}/{}/used_aux_invs.txt'.format(self.data_dir, self.protocol_name)

        if string_list:
            with open(fout, 'a') as f:
                f.write('-- Auxiliary invariants used by {}:\n{}\n\n'.format(rulename, '\n'.join(
                    string_list)))
            print('-- Auxiliary invariants used by {}: {}'.format(rulename, len(string_list)))

    def sparse_rule(self, rule_text, param_name_dict):
        pattern = re.compile(r'rule\s*\"(.*?)\"\s*(.*?)==>.*?begin(.*?)endrule\s*;', re.S)
        rule_name, guards, actions = pattern.findall(rule_text)[0]
        guard_obj = Guard(guards, param_name_dict)
        guard_obj.sparse()
        action_obj = Action(actions, param_name_dict)
        action_obj.sparse()
        return rule_name, guard_obj, action_obj


class Reiner(object):
    def __init__(self, rulename, guard_obj, aux_invs):
        self.rulename = rulename
        self.guard_obj = guard_obj
        self.aux_invs = aux_invs
        self.dict_inv2index = {}
        self.dict_index2inv = {}
        self.construct_dicts()
        self.used_inv_index = set()

    def construct_dicts(self):
        print('type fo self.aux_invs = {}'.format(type(self.aux_invs)))
        for i, aux_inv in enumerate(self.aux_invs, 1):
            self.dict_index2inv[i] = aux_inv
            self.dict_inv2index[' & '.join(aux_inv[0]) + ' -> ' + aux_inv[1]] = i

    def map_index_to_inv(self):
        used_inv = []
        for index in self.used_inv_index:
            used_inv.append(self.dict_index2inv[index])
        return used_inv

    def find_useful_invs(self, boundary_K, guard=set()):
        if not guard:
            guard = self.guard_obj.normal_guards
            guard = set(guard)

        temp_k = 0
        iter_cons = set()

        for k in range(boundary_K):
            # while temp_k < boundary_K:
            iter_cons |= self.find_useful_invs_iter(guard | iter_cons)
            print("Strengthening {} time, find {} predicates".format(k + 1, len(iter_cons)))
        # while temp_k <= boundary_K and iter_cons != (self.find_useful_invs_iter(guard | iter_cons)):
        #     iter_cons = self.find_useful_invs_iter(guard | iter_cons)
        used_invset = self.map_index_to_inv()
        self.evaluate(used_invset)
        return used_invset, self.used_inv_index

    def find_useful_invs_iter(self, guard):
        useful_cond = set()
        for i, (pre, cond) in enumerate(self.aux_invs, 1):
            if set(guard) & pre == pre:
                useful_cond.add(cond)
                # record used aux invs
                if cond not in set(guard):
                    self.used_inv_index.add(i)
        return useful_cond

    def evaluate(self, used_invset):
        if not used_invset:
            return
        print("\n[Candidate association rules used by {}]: {}".format(self.rulename, len(used_invset)))
        # for i, (pre, cond) in enumerate(used_invset, 1):
        #     print("\t%d: %s -> %s" % (i, ' & '.join(pre), cond))


class Abstractor(object):
    def __init__(self, rulename, guard_obj, action_obj, abs_type, aux_invs, all_types, logfile, dict_inv2index):
        self.rulename = rulename
        self.guard_obj = guard_obj
        self.action_obj = action_obj
        self.abs_type = abs_type
        self.aux_invs = aux_invs
        self.all_types = all_types
        self.print_string = ""
        self.used_inv_string_list = []
        self.logfile = logfile
        self.dict_inv2index = dict_inv2index

    def rep_global(self, aux_inv_list, action_obj, abs_para_list):
        new_action_content = []
        rep_dict, added_dict = {}, {}
        rep_dict_to_string = {}

        def check_other_types(all_types, stmt, origin_dict):
            temp_dict = {}
            for t in all_types:
                finds = re.findall(r'%s\_\d' % t, stmt)
                for find in finds:
                    if find not in origin_dict:
                        temp_dict[find] = t
            return temp_dict

        for pre, cond in aux_inv_list:
            if not pre or not cond: continue
            if re.findall('!', cond):
                continue
            parts = re.split(r'\s=\s', cond)
            # print('cond = {}, part = {}'.format(cond, parts))

            left, right = parts[0], parts[1]
            if not re.findall(r'\[', right):
                rep_dict[left] = right
                rep_dict_to_string[left] = (' & '.join(pre) + ' -> ' + ''.join(cond))

        is_repl = False
        for stmt in list(filter(lambda x: re.findall(':=', x), action_obj.mainfield.content)):
            assign = re.split(r':=\s*.*?', stmt)[1]
            for abs_para in abs_para_list:
                if re.findall(r'%s' % abs_para, assign):
                    if assign in rep_dict:
                        is_repl = True
                        stmt = stmt.replace(assign, rep_dict[assign])
                        added_dict.update(check_other_types(self.all_types, stmt, self.action_obj.mainfield.para_dict))
                        self.used_inv_string_list.append(rep_dict_to_string[assign])
                        open(self.logfile, 'a').write(
                            'replace: {}\n'.format(self.dict_inv2index[rep_dict_to_string[assign]]))

            new_action_content.append(stmt)
        if not is_repl:
            open(self.logfile, 'a').write('rule used for replace: []\n')
        self.action_obj.mainfield.content = new_action_content
        self.action_obj.mainfield.para_dict.update(added_dict)

    def abstract(self):
        main_para = self.guard_obj.mainfield.para_dict
        cnt = 0
        for v in main_para.values():
            if v == self.abs_type: cnt += 1
        print('\ninclude %d abstract type' % cnt)

        if cnt == 0:
            print('\nRule {} has no parameter.'.format(self.rulename))
            return
        elif cnt == 1:
            print('\nRule {} has 1 parameter.'.format(self.rulename))
            self.abstract_1_para()
        elif cnt == 2:
            print('\nRule {} has 2 parameter.'.format(self.rulename))
            self.abstract_2_para()
        else:
            print('Too many abstracted types, cannot symmetrically abstract!')

    def abstract_inv(self, inv_list, abs_para_list):
        abs_inv = []
        for pre, cond in inv_list:
            for abs_para in abs_para_list:
                if self.abstract_list(abs_para, [cond]):
                    abs_inv.append(cond)
                    self.used_inv_string_list.append("{} -> {}".format(' & '.join(pre), cond))
        return list(set(abs_inv))

    def asbtract_obj(self, origin_obj, abs_para_list):
        for abs_para in abs_para_list:
            origin_obj.mainfield.content = self.abstract_list(abs_para, origin_obj.mainfield.content)

            index = 0
            while index < len(origin_obj.forfield) and origin_obj.forfield:
                origin_obj.forfield[index].content = self.abstract_list(abs_para, origin_obj.forfield[index].content)
                index += 1

            index = 0
            while index < len(origin_obj.existfield) and origin_obj.existfield:
                origin_obj.existfield[index].content = self.abstract_list(abs_para,
                                                                          origin_obj.existfield[index].content)
                index += 1
        return [origin_obj]

    def abstract_list(self, abs_para, waiting_list):
        if not abs_para:
            abs_para = abs_para
        rest_list = []
        for wl in waiting_list:
            if not re.findall(r'\[%s\]' % abs_para, wl):
                if re.findall(r'%s' % abs_para, wl):
                    wl = re.sub(r'%s' % abs_para, 'Other', wl)
                rest_list.append(wl)

        return rest_list

    def abstract_1_para(self, abs_para_list: list = None):
        def check_empty(abs_obj):
            for index in range(len(abs_obj.forfield)):
                if abs_obj.forfield[index].content:
                    return False
            for index in range(len(abs_obj.existfield)):
                if abs_obj.existfield[index].content:
                    return False
            if abs_obj.mainfield.content:
                return False
            return True

        if not abs_para_list:
            abs_para_list = [self.abs_type + '_1']
        print('abstract parameter: {}'.format(', '.join(abs_para_list)))

        self.rep_global(self.aux_invs, self.action_obj, abs_para_list)

        abs_action_obj = self.asbtract_obj(self.action_obj, abs_para_list)[0]
        abs_guard_obj = self.asbtract_obj(self.guard_obj, abs_para_list)[0]
        abs_inv = self.abstract_inv(self.aux_invs, abs_para_list)

        if check_empty(abs_action_obj):
            print('action part is empty')
            self.print_string += '\n\n-- No abstract rule for rule {}\n\n'.format(self.rulename)
            open(self.logfile, 'a').write('NoAbstractRule')
        else:
            # log
            open(self.logfile, 'a').write(
                'abstract node: [{}],'.format(','.join(map(lambda x: transform(x), abs_para_list))))
            # open(self.logfile, 'a').write(
            #     '[{}]'.format(','.join(map(lambda x: 'rule_{}'.format(self.dict_inv2index[x])), )))
            # print('write abstract rules')
            self.print_abs_rule(abs_guard_obj, abs_action_obj, abs_inv, abs_para_list, prefix='_'.join(abs_para_list))

            open(self.logfile, 'a').write('\naux_invs: \n[{}]'.format(
                ',\n'.join(map(lambda x: 'rule_{}: {}'.format(self.dict_inv2index[x], x),
                             self.used_inv_string_list))))

    def abstract_2_para(self):
        abs_para = [self.abs_type + '_1']
        self.abstract_1_para(abs_para)

        abs_para = [self.abs_type + '_2']
        self.abstract_1_para(abs_para)

        abs_para = [self.abs_type + '_1', self.abs_type + '_2']
        self.abstract_1_para(abs_para)

    def evaluate(self, abs_guard_obj, abs_action_obj, abs_inv, abs_para_list, prefix=""):
        print('ABS_%s%s' % (self.rulename, prefix))
        abs_guard_obj.print_value(title='ABS_%s%s guard' % (self.rulename, prefix))
        abs_action_obj.print_value(title='ABS_%s%s action' % (self.rulename, prefix))
        print('abs_inv', abs_inv)

    def print_abs_rule(self, abs_guard_obj, abs_action_obj, abs_inv, abs_para_list, prefix=""):
        print('\nPrint abstract rule of {}, abstract {}'.format(self.rulename, ','.join(abs_para_list)))

        def pop_key_from_field_list(temp_obj, k_list):
            new_obj = copy.deepcopy(temp_obj)
            for item in new_obj.forfield:
                for k in k_list:
                    item.para_dict.pop(k)

            for item in new_obj.existfield:
                for k in k_list:
                    item.para_dict.pop(k)
            return new_obj

        para_dict = abs_guard_obj.mainfield.para_dict.copy()
        try:
            for k in abs_para_list:
                if k in para_dict:
                    para_dict.pop(k)
        except getopt.GetoptError:
            sys.stderr.write(
                'Cannot find some of [{}] in [{}]'.format(','.join(abs_para_list), ','.join(para_dict.keys())))
        else:
            main_list = [k for k in abs_guard_obj.mainfield.para_dict.keys()]
            print_string = ""

            if len(para_dict) >= 1:
                print_string = print_string + '\n\nruleset %s do' % '; '.join(
                    ('{} : {}'.format(k, v) for k, v in para_dict.items()))

            print_string += '\nrule \"ABS_%s_%s\"\n' % (self.rulename, prefix)

            guard_string = self.print_guard(
                pop_key_from_field_list(abs_guard_obj, set(abs_para_list) | set(main_list)))
            inv_string = self.print_inv(abs_inv, para_dict)

            if guard_string and inv_string:
                print_string += '\n \t& '.join([guard_string, inv_string])
            elif guard_string and not inv_string:
                print_string += guard_string
            elif not guard_string and inv_string:
                print_string += inv_string
            else:
                print_string += '\n\tTrue'

            print_string += '\n==>\nbegin'

            for k in main_list:
                if k in abs_action_obj.mainfield.para_dict:
                    abs_action_obj.mainfield.para_dict.pop(k)

            print_string = print_string + self.print_action(
                pop_key_from_field_list(abs_action_obj, set(abs_para_list) | set(main_list)))

            print_string = print_string + '\nendrule;'
            if len(para_dict) >= 1:
                print_string += '\nendruleset;\n\n'

            self.print_string += print_string

    def print_inv(self, abs_inv, para_dict):
        if not abs_inv: return ""
        cur_para_dict = {}
        print_string = ""
        for cur_type in self.all_types:
            for ai in abs_inv:
                for _, type_para in enumerate(re.findall(r'%s\_\d' % cur_type, ai), 1):
                    cur_para_dict['%s' % (type_para)] = cur_type
        for para in para_dict:
            if para in cur_para_dict:
                cur_para_dict.pop(para)

        if len(cur_para_dict) >= 1:
            print_string = print_string + '\n\tforall %s do\n\t\t' % '; '.join(
                ('{} : {}'.format(k, v) for k, v in cur_para_dict.items()))

        print_string = print_string + ' &\n\t\t'.join(abs_inv)
        if len(cur_para_dict) >= 1:
            print_string = print_string + '\n\tend'

        return print_string

    def print_guard(self, guard_obj):
        # print('\nenter print_guard')
        def judge(stmt):
            return stmt
            # if re.findall('Other', stmt):
            #     # print(stmt)
            #     if re.findall(r'!=', stmt):
            #         return str(len(set(map(lambda x: x.strip(' '), re.split(r'!=', stmt)))) != 1)
            #     elif re.findall(r'=', stmt):
            #         return str(len(set(map(lambda x: x.strip(' '), re.split(r'=', stmt)))) == 1)
            #     else:
            #         return stmt
            # else:
            #     return stmt

        print_string = ""

        if guard_obj.mainfield.content:
            print_string = print_string + '\n\t' + ' &\n\t'.join(map(lambda x: judge(x), guard_obj.mainfield.content))

        for for_item in guard_obj.forfield:
            if not for_item.content:
                continue
            print_string += ('\n\t& forall {}'.format('; '.join(
                ('{} : {}'.format(k, v) for k, v in
                 for_item.para_dict.items()))) + ' do' + '\n\t\t\t' +
                             ' &\n\t\t'.join(map(lambda x: judge(x), for_item.content))
                             + '\n\tend')

        for exist_item in guard_obj.existfield:
            if not exist_item.content: continue
            print_string = print_string + '\t& exists {}'.format('; '.join(
                ('{} : {}'.format(k, v) for k, v in
                 exist_item.para_dict.items()))) + ' do' + '\n\t\t' + ' &\n\t\t'.join(
                map(lambda x: judge(x), exist_item.content)) + '\n\tend'

        return print_string

    def print_action(self, action_obj):
        def judge(stmt):
            # if re.findall('Other', stmt):
            #     if re.findall(r'Other\s?=\s?Other', stmt):
            #         stmt = re.sub(r'Other\s?=\s?Other', 'true', stmt)
            #         # return str(True)
            #     elif re.findall(r'Other\s?!=\s?Other', stmt):
            #         stmt = re.sub(r'Other\s?!=\s?Other', 'false', stmt)
            #         # return str(False)
            #     elif re.findall(r'Other\s?!=\s?(\w+)', stmt):
            #         stmt = re.sub(r'Other\s?!=\s?(\w+)', 'true', stmt)
            #         # return str(True)
            #     elif re.findall(r'(\w+)\s?!=\s?Other', stmt):
            #         stmt = re.sub(r'(\w+)\s?!=\s?Other', 'true', stmt)
            #     elif re.findall(r'Other\s?=\s?(\w+)', stmt):
            #         stmt = re.sub(r'Other\s?=\s?(\w+)', 'false', stmt)
            #     elif re.findall(r'(\w+)\s?=\s?Other', stmt):
            #         stmt = re.sub(r'(\w+)\s?=\s?Other', 'false', stmt)
            #         # return str(False)
            #     # else:
            return stmt

        print_string = ""
        if action_obj.mainfield.para_dict:
            print_string += ('\n\tfor {}'.format('; '.join(
                ('{} : {}'.format(k, v) for k, v in
                 action_obj.mainfield.para_dict.items()))) + ' do' + '\n\t\t\t' + '; \n\t\t'.join(
                map(lambda x: judge(x), action_obj.mainfield.content)) + ';\n\tend')
        elif action_obj.mainfield.content:
            print_string += '\n\t{};'.format(' ;\n\t'.join(map(lambda x: judge(x), action_obj.mainfield.content)))

        for for_item in action_obj.forfield:
            if not for_item.content or not for_item.para_dict.items():
                # print('\n\n{},{}\n\n'.format(for_item.content,for_item.para_dict))
                continue

            print_string = print_string + '\n\tfor ' + '; '.join(
                ('{} : {}'.format(k, v) for k, v in for_item.para_dict.items())) + ' do'
            print_string = print_string + '\n\t\t'  # + ' ;\n\t\t'.join(for_item.content)
            i = 0
            if_flag = False
            while i < len(for_item.content):
                tmp = for_item.content[i]
                if for_item.content[i] in {'if', 'elsif'}:
                    if_flag = True
                    print_string += for_item.content[i] + ' '
                elif for_item.content[i] in {'else'}:
                    print_string += for_item.content[i] + ' '
                elif for_item.content[i] in {'endif', 'end'}:
                    print_string += for_item.content[i] + '\n '
                elif for_item.content[i] in {'then'}:
                    if_flag = False
                    print_string += for_item.content[i] + '\n '
                elif i > 0 and if_flag:  # for_item.content[i - 1] in {'if', 'elsif'}:
                    print_string += judge(for_item.content[i]) + ' \n\t\t'
                    if for_item.content[i + 1] not in {'else', 'then', 'elsif'}:
                        print_string += ' & '
                elif not for_item.content[i].startswith('for'):
                    print_string += judge(for_item.content[i]) + ' ;\n\t\t'
                i += 1
            print_string = print_string + ';\n\tendfor;'

        for exist_item in action_obj.existfield:
            if not exist_item.content: continue
            print_string = print_string + '\n\texists ' + '; '.join(
                ('{} : {}'.format(k, v) for k, v in exist_item.para_dict.items())) + ' do'
            print_string = print_string + '\n\t\t'  # + ' ;\n\t\t'.join(exist_item.content)
            i = 0
            if_flag = False
            while i < len(exist_item.content):
                if exist_item.content[i] in {'if', 'elsif', 'else'}:
                    if_flag = True
                    print_string += exist_item.content[i] + ' '
                elif exist_item.content[i] in {'then', 'endif', 'end'}:
                    if_flag = False
                    print_string += exist_item.content[i] + '\n '
                elif i > 0 and if_flag:  # for_item.content[i - 1] in {'if', 'elsif'}:
                    print_string += judge(exist_item.content[i]) + ' \n\t\t'
                    if exist_item.content[i + 1] not in {'else', 'then', 'elsif'}:
                        print_string += ' & '
                else:
                    print_string += exist_item.content[i] + ' ;\n\t\t'
                i += 1
        return print_string


def analyzeParams(params):
    """
    @param params: as `i:Node; j:Node`
    @return a tuple as `{'i': 'Node', 'j': 'Node'}
    """
    if not params: return {}, '[]'
    parts = params.split(';')
    param_name_dict = {}
    for p in parts: param_name_dict[p.split(':')[0].strip()] = p.split(':')[1].strip()

    return param_name_dict


class Protocol(object):
    def __init__(self, data_dir, protocol_name, file_url):
        self.data_dir = data_dir
        self.protocol_name = protocol_name
        self.file_url = file_url
        self.logfile = '{}/{}/prot.abs'.format(self.data_dir, self.protocol_name)

    def read_file(self):
        return open(self.file_url).read()

    def show_config(self):
        text = self.read_file()
        config = re.findall(r'(\w+)\s*:\s*(\d+)\s*;', text)
        for name, num in config:
            print('{} : {}'.format(name, num))

    def collect_atoms(self):
        text = self.read_file()
        typedf = TypeDef(text)
        ruleset = Ruleset(self.data_dir, self.protocol_name, text, typedf.para)
        ruleset.collect_atoms_from_ruleset()
        with open('{}/{}/collected_atom.txt'.format(self.data_dir, self.protocol_name), 'w') as f:
            f.write('\n'.join(ruleset.atoms))
        print('Find atomic predicates: %d\n' % (len(ruleset.atoms)))
        return typedf.type

    def refine_abstract(self, aux_invs, abs_type, print_usedinvs_to_file=False, boundary_K=1):
        text = self.read_file()
        typedf = TypeDef(text)
        ruleset = Ruleset(self.data_dir, self.protocol_name, text, typedf.type.keys())
        ruleset.sparse_rulesets(aux_invs, abs_type, boundary_K, self.logfile, print_usedinvs_to_file)
        return ruleset.print_info, list(ruleset.used_inv_string_set)
