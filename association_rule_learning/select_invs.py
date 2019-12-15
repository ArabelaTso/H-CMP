import re
import os
import sys
import multiprocessing
from shutil import copyfile

from murphi_analysis.call_murphi import run_murphi


class SlctInv(object):
    def __init__(self, data_dir, name, par, all_types, home=False):
        self.data_dir = data_dir
        self.name = name
        self.home = home
        self.murphi_dir = self.loc_murphi_dir()
        self.par = par
        self.all_types = all_types
        self.counterex_index = []
        # self.test_rules = {'rule_%d' % i: rule for i, rule in enumerate(test_rules, 1)}

    # def update_test_rules(self, new_set):
    #     self.test_rules = {'rule_%d' % i: rule for i, rule in enumerate(new_set, 1)}

    def select_invariant(self, test_rule_string, keep_file, num_core=multiprocessing.cpu_count(), original_file=None,
                         aux_para=""):
        print('\nchecking invariants...')
        original_file = "{0}/{1}/{1}.m".format(self.data_dir, self.name) if original_file is None else original_file

        test_rule_string_dict = {'rule_%d' % i: rule for i, rule in enumerate(test_rule_string, 1)}
        translate_dic = self.translate_test_inv(test_rule_string_dict)

        n = len(test_rule_string)
        if n < 100:
            num_core = num_core
        else:
            num_core = min(num_core, n // 100)
        print('num core = {}, type = {}'.format(num_core, type(num_core)))
        jobs = [(i * n // num_core, (i + 1) * n // num_core) for i in range(num_core)]

        print('ranges', jobs)
        spurious_index = []
        # try:
        with multiprocessing.Pool(num_core) as p:
            spurious_index.extend(p.starmap(self.parallel,
                                            [(index_range, pid, translate_dic, original_file, keep_file, aux_para)
                                             for
                                             pid, index_range
                                             in enumerate(jobs, 1)]))

        spurious_index = list(set(k for key in spurious_index for k in key))
        self.counterex_index = spurious_index
            # print(self.counterex_index)
        # except:
        #     print('[ERROR!!!] Run Murphi failed!')
        #     sys.exit(1)

        print('original rule: {}, remove {}, remain {}'.format(n, len(spurious_index), n - len(spurious_index)))
        self.counterex_index = list(map(lambda x: int(''.join(re.findall('\_(\d*)', x))) - 1, self.counterex_index))
        return len(spurious_index), self.counterex_index

    def loc_murphi_dir(self):
        if not os.path.exists('murphi_url.txt'): raise FileExistsError
        return open('murphi_url.txt').read().strip()

    def translate_test_inv(self, test_rule_string_dict):
        # test_invs is empty
        if not test_rule_string_dict: return []

        translate_dic = {}
        for key, rule in test_rule_string_dict.items():
            translate_dic.update(
                {key: '\n\nInvariant \"%s\"\n' % key + self.to_murphi(rule)})
        return translate_dic

    def parallel(self, index_range, id, translate_dic, original_file, keep_file, aux_para=""):
        start, end = index_range
        counters = []
        new_file = '{0}/{1}/ABS_{1}_{2}.m'.format(self.data_dir, self.name, id)
        print('new_file = {}'.format(new_file))
        # new_file = "{}_{}.m".format(original_file.split('.')[0], id)
        copyfile(original_file, new_file)
        with open(new_file, 'a') as f:
            for rule_num in range(start + 1, end + 1):
                f.writelines(translate_dic['rule_%d' % rule_num])
        counter_ex_list = run_murphi(self.data_dir, self.name, self.murphi_dir, aux_para)

        # for counter_ex in counter_ex_list:
        if len(counter_ex_list):
            for counter_ex in counter_ex_list:
                if not re.findall('rule_\d', counter_ex):
                    print(counter_ex)
                    break
                counters.append(counter_ex)

                # pattern = re.compile(r'Invariant \"%s\".*?;\n' % counter_ex, re.S)
                # new_content = re.sub(pattern, '', open(new_file).read())
                print('remove %s' % counter_ex)

            # with open(new_file, 'w') as fw:
            # fw.writelines(new_content)
            # counter_ex_list = self.run_murphi(new_file)

        if not keep_file:
            os.remove(new_file)
        # os.remove("{}.cpp".format(new_file.split('.')[0]))
        # os.remove("{}.o".format(new_file.split('.')[0]))
        print(counters)
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

    def check_usedF(self, test_rule_string, num_core=multiprocessing.cpu_count(), original_file=None, aux_para="",
                    keep_file=False):
        original_file = "{0}/{0}.m".format(self.name) if original_file is None else original_file
        print('checking %s' % original_file)
        spurious_cnt, counterex_index = self.select_invariant(test_rule_string, keep_file=keep_file, num_core=num_core,
                                                              original_file=original_file, aux_para=aux_para)
        print('counterex_index', counterex_index)
        if not spurious_cnt:
            print('usedF all passed!')
        else:
            print('usedF failed.')
            print(spurious_cnt)

        return counterex_index
