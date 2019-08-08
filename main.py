# -*- coding: utf-8 -*-
# @Author  : arabela
import os
import re
import sys
import time
import getopt
import copy
import subprocess
import collections
from collections import OrderedDict
import multiprocessing
import preprocess as preprocess
import analyser as analyser
from shutil import copyfile

prefix_msg = '''
==========================================================================
Welcome to H-CMP
1. Please make sure you have installed CMurphi properly, and 
   write CMurphi's location into murphi_url.txt. 
        E.g. /home/usr/cmurphi5.4.9.1/
2. We provide several testing protocols including:
        MutualExclusion, Mesi, Meosi, German, and Flash.
==========================================================================
'''

help_msg = '''
Usage:
Options:
1) General: (default: -n 2)
	-h            help.
	-p            protocol name
	-n <n>        number of node used for verification
	              (protocols with only homogenerous nodes -- 2
	               protocols with a heterogenerous node   -- 3)
2) Learning process: (default: -f 2, -s -0, -c 1)
	-l            load the existing auxiliary invariants. 
	              (if file "aux_invs_copy.txt" in the correspondent folder)
	-f <n>        the size of frequent set
	-s <n>        the minimun support in association rule learning 
	-c <n>        the minimun confidence in association rule learning
2) Other options: (default: -k 2)
	-k <n>        number of processor
==========================================================================
'''


def run_murphi(file, aux_para=''):
    file = file.split('.')[0]
    if not os.path.exists('murphi_url.txt'):
        raise FileExistsError
    else:
        murphi_dir = open('murphi_url.txt').read().strip()

    print('Generate reachable set by Murphi...')
    process1 = subprocess.Popen("{0}/src/mu {1}.m".format(murphi_dir, file), shell=True,
                                stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE)

    (stdout, stderr) = process1.communicate()
    if not re.search(r'Code generated', stdout.decode('utf-8')):
        print(stderr.decode('utf-8'))
        raise ValueError

    command2 = "g++ -ggdb -o {0}.o {0}.cpp -I {1}/include -lm".format(file, murphi_dir)

    process2 = subprocess.Popen(command2, shell=True,
                                stdout=subprocess.PIPE,
                                stderr=subprocess.PIPE)
    process2.communicate()

    process = subprocess.Popen("{0}.o -k10000000 {1}".format(file, aux_para), shell=True,
                               stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE)

    (stdoutdata, stderrdata) = process.communicate()

    pattern_counter = re.compile(r'Invariant\s"(\w+).*"\sfailed')
    counter_ex = re.findall(pattern_counter, stdoutdata.decode('utf-8'))
    if len(counter_ex): print("%s failed!" % counter_ex[0])

    os.remove('%s.cpp' % file)
    os.remove('%s.o' % file)

    return counter_ex[0] if len(counter_ex) else 0


class TimeRecorder(object):
    def __init__(self, protocol_name):
        self.protocol_name = protocol_name
        self.time_stamps = collections.defaultdict(str)
        self.fileaname = "{0}/time_report.txt".format(protocol_name)

    def add_time(self, what, dur):
        self.time_stamps[what] = dur

    def report(self):
        print('\nRunning Time Report for {}:\n'.format(self.protocol_name))
        with open(self.fileaname, 'w') as fw:
            for what, dur in self.time_stamps.items():
                print("{}: {}".format(what, dur))
                fw.write("{}: {}\n".format(what, dur))


if __name__ == "__main__":
    try:
        if not os.path.exists('./murphi_url.txt'):
            print('murphi_url.txt does not exists! Please create!')
            sys.exit()

        with open('./murphi_url.txt', 'r') as f:
            murphi_url = f.read().strip()

        if not murphi_url:
            sys.stderr.write('Empty murphi_url.txt, please check again.')
            sys.exit()
        if not os.path.exists(murphi_url):
            sys.stderr.write('Wrong murphi url, please check url in murphi_url.txt again.')
            sys.exit()

        sys.stderr.write(prefix_msg)

        # opts, args = getopt.getopt(sys.argv[1:], 'p:a:n:c:k:z:h',
        #                            ['protocol=', 'abs_type=', 'node=', 'core=', 'kmax=', 'z3=', 'help'])
        opts = [('-p', 'flash2'), ('-a', 'NODE'), ('-c', 1), ('-k', 3), ('-n', 2), ('-z', 1)]

        protocol_name, abs_type = '', ''
        NODE_NUM, set_n, min_support, min_config, kmax, num_core, z3 = 2, 3, 0.0, 1.0, 3, multiprocessing.cpu_count(), 0

        for opt, arg in opts:
            if opt in ('-h', '--help'):
                sys.stdout.write(help_msg)
                sys.exit(0)
            elif opt in ('-p', '--protocol'):
                protocol_name = arg
            elif opt in ('-n', '--node'):
                NODE_NUM = int(arg)
            elif opt in ('-a', '--abs_type'):
                abs_type = arg
            elif opt in ('-k', '--kmax'):
                kmax = int(arg)
            elif opt in ('-c', '--core'):
                num_core = int(arg)
            elif opt in ('-z', '--z3'):
                z3 = int(arg)
            else:
                print('Wrong input!\n')
                sys.stderr.write(help_msg)
                sys.exit(1)
        home_flag = (NODE_NUM != 2)

        if not protocol_name or not abs_type:
            sys.stderr.write('Please input protocol name and abstract type!')
            sys.exit(1)

    except getopt.GetoptError:
        sys.stderr.write(help_msg)
        sys.exit()

    else:
        fileaname = "{0}/{0}.m".format(protocol_name)
        print('*' * 50)
        print('Protocol: %s' % protocol_name)
        print("NODE_NUM={}, set_n={}, min_support={}, min_config={}, kmax={}num_core={}, z3={}".format(NODE_NUM, set_n,
                                                                                                       min_support,
                                                                                                       min_config,
                                                                                                       kmax, num_core,
                                                                                                       z3))
        print('*' * 50)

        # create abstract protocol file
        abs_filename = "{0}/ABS_{0}.m".format(protocol_name)
        copyfile(fileaname, abs_filename)

        # set auxinv_filename
        auxinv_filename = "{0}/aux_invs.txt".format(protocol_name)
        asso_filename = "{0}/assoRules.txt".format(protocol_name)

        time_record = TimeRecorder(protocol_name)

        # set start time
        total_start = time.time()

        # create reachable set file if not available
        if not os.path.exists("{0}/{0}.txt".format(protocol_name)):
            # start collecting reachable set
            start_time = time.time()
            run_murphi('{0}/{0}.m'.format(protocol_name), '-ta >{0}/{0}.txt'.format(protocol_name))
            # end collecting reachable set
            time_record.add_time('reachableset', '%.2f' % (time.time() - start_time))
        else:
            time_record.add_time('reachableset', '0.00')

        protocol = analyser.Protocol(protocol_name, fileaname)
        all_types = protocol.collect_atoms()
        print(all_types)

        # if auxiliary invariants already exist.
        if os.path.exists(auxinv_filename):
            aux_invs = []
            with open(auxinv_filename, 'r') as fr:
                content = list(map(lambda x: x.split(': ')[1], filter(lambda x: x, fr.read().split('\n'))))

            for line in content:
                pre = set(line.strip().split(' -> ')[0].split(' & '))
                cond = line.strip().split(' -> ')[1]
                aux_invs.append((pre, cond))
            print('read %d auxiliary invariants' % (len(aux_invs)))
            time_record.add_time('auxiliary', '0.00')
        else:
            # if association rules already exist.
            if os.path.exists(asso_filename):
                rule_tuple = []
                with open(asso_filename, 'r') as fr:
                    rule_string_list = list(map(lambda x: x.split(': ')[1], filter(lambda x: x, fr.read().split('\n'))))

                for line in rule_string_list:
                    pre = set(line.strip().split(' -> ')[0].split(' & '))
                    cond = line.strip().split(' -> ')[1]
                    rule_tuple.append((pre, cond))
                print('read %d association rules' % (len(rule_tuple)))
                time_record.add_time('association', '0.00')
            else:
                # need to learn association rules
                # start preprocessing
                start_time = time.time()
                od = OrderedDict()
                od['NODE_1'] = 'Home'
                od['NODE_2'] = 'NODE_1'
                od['NODE_3'] = 'NODE_2'
                replace_index = None if NODE_NUM == 2 else od
                # OrderedDict(
                # {'NODE_1': 'Home', 'NODE_2': 'NODE_1', 'NODE_3': 'NODE_2'})
                processor = preprocess.DataProcess(protocol_name, replace_index=replace_index)
                dataset, itemMeaning, para_digit = processor.execute(load=False)
                # end preprocessing
                time_record.add_time('preprocess', '%.2f' % (time.time() - start_time))

                global_vars = processor.select_global(itemMeaning)
                print('global vars:', global_vars)

                # learning association rules
                # start association rule learning
                start_time = time.time()
                learner = preprocess.RuleLearing(protocol_name, dataset, itemMeaning, global_vars=global_vars,
                                                 max_freq_size=kmax)
                rule_tuple, rule_string_list = learner.execute()
                # end association rule learning
                time_record.add_time('association', '%.2f' % (time.time() - start_time))
                assert len(rule_tuple) == len(rule_string_list)

            # select candidate invs
            instantiator = preprocess.RuleLearing(protocol_name, [], {})
            instan_rule_tuple, _ = instantiator.instantiate(rule_tuple, rule_string_list, all_types)
            _, candidate_inv_string = protocol.refine_abstract(instan_rule_tuple, abs_type=abs_type)
            candidate_inv_string = list(set(candidate_inv_string))
            candidate_inv_tuple = list(map(lambda x: preprocess.split_string_to_tuple(x), candidate_inv_string))
            assert len(candidate_inv_string) == len(candidate_inv_tuple)
            print('select candidate association rules: before: {}, after: {}'.format(len(instan_rule_tuple),
                                                                                     len(candidate_inv_tuple)))

            with open('{}/candidate_rules.txt'.format(protocol_name), 'w') as f:
                for cnt, stmt in enumerate(sorted(candidate_inv_string, key=lambda x: len(x)), 1):
                    f.write('rule_%d: %s\n' % (cnt, stmt))

            # minimize candidate invs, because runnign murphi costs lots of time
            minimzer = preprocess.RuleLearing(protocol_name, [], {})
            rule_tuple, rule_string_list = minimzer.symmetry_reduction(candidate_inv_tuple, candidate_inv_string,
                                                                       all_types)
            # remove spurious invariants
            # start removing spurious invariants
            start_time = time.time()
            selector = preprocess.SlctInv(protocol_name, [], all_types, home=home_flag)
            _, counterex_index = selector.select_invariant(rule_string_list, num_core,
                                                           '{0}/{0}.m'.format(protocol_name),
                                                           aux_para="-finderrors -ndl")
            # end removing spurious invariants
            time_record.add_time('auxiliary', '%.2f' % (time.time() - start_time))

            tmp_tuple, tmp_string = copy.deepcopy(rule_tuple), copy.deepcopy(rule_string_list)
            for cex in counterex_index:
                tmp_tuple.remove(rule_tuple[cex])
                tmp_string.remove(rule_string_list[cex])
            rule_tuple, rule_string_list = tmp_tuple, tmp_string

            # instantiate invariants using symmetry expansion
            instantiator = preprocess.RuleLearing(protocol_name, [], {})
            aux_invs, aux_inv_string = instantiator.instantiate(rule_tuple, rule_string_list, all_types)

        # refine and abstract
        # start refining and abstracting
        start_time = time.time()
        print_info, used_inv_string_list = protocol.refine_abstract(aux_invs, abs_type=abs_type)
        # end removing spurious invariants
        time_record.add_time('strengthening', '%.2f' % (time.time() - start_time))

        # write to abstract file
        with open(abs_filename, 'a') as fw:
            fw.write(print_info)

        # check used invariants and abstract protocol
        # start checking
        start_time = time.time()
        max_cnt = 1
        print('\n\n-----------------\nNo. %d' % max_cnt)
        checker = preprocess.SlctInv(protocol_name, [], all_types, home=home_flag)
        counterex_index = checker.check_usedF(used_inv_string_list, num_core, abs_filename, aux_para="-finderrors -ndl")

        if counterex_index:
            # if still exists counterexample after strengthening,
            # then iterate until max_cnt or no counterexample
            max_cnt += 1
            new_inv_tuple, new_string_list = [], []
            while counterex_index and max_cnt < 10:
                print('\n\n-----------------\nNo. %d' % max_cnt)

                tmp_string = copy.deepcopy(used_inv_string_list)
                for cex in counterex_index:
                    tmp_string.remove(used_inv_string_list[cex])
                new_string_list = tmp_string
                new_inv_tuple = list(map(lambda x: preprocess.split_string_to_tuple(x), new_string_list))

                new_absfile = "{0}/ABS_{0}_{1}.m".format(protocol_name, max_cnt)
                copyfile(fileaname, new_absfile)

                print_info, used_inv_string_list = protocol.refine_abstract(new_inv_tuple, abs_type=abs_type)
                with open(new_absfile, 'a') as fw:
                    fw.write(print_info)
                checker = preprocess.SlctInv(protocol_name, [], all_types, home=home_flag)
                counterex_index = checker.check_usedF(used_inv_string_list, num_core, new_absfile, "-finderrors -ndl")
                max_cnt += 1
            if counterex_index:
                print('\nCounter-examples:{}\n'.format(counterex_index))
        else:
            print('End verifing, no counter-examples')

        # print time record
        time_record.add_time('final-check', '%.2f' % (time.time() - start_time))
        time_record.add_time('total', '%.2f' % (time.time() - total_start))
        time_record.add_time('iter', max_cnt)
        time_record.report()
