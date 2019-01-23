# -*- coding: utf-8 -*-
# @Author  : arabela

import os
import re
import copy
import subprocess
import preprocess as preprocess
import analyser as analyser
from shutil import copyfile


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


if __name__ == "__main__":
    # protocol name
    protocol_name = "godsont-1n2c"
    fileaname = "{0}/{0}.m".format(protocol_name)
    print('Protocol: %s' % protocol_name)

    # create abstract protocol file
    abs_filename = "{0}/ABS_{0}.m".format(protocol_name)
    copyfile(fileaname, abs_filename)

    # set auxinv_filename
    auxinv_filename = "{0}/aux_invs.txt".format(protocol_name)
    asso_filename = "{0}/assoRules.txt".format(protocol_name)

    # define abstract type
    abs_type = 'TYPE_CACHE'
    num_core = 16

    # create reachable set file if not available
    if not os.path.exists("{0}/{0}.txt".format(protocol_name)):
        run_murphi('{0}/{0}.m'.format(protocol_name), '-ta >{0}/{0}.txt'.format(protocol_name))

    protocol = analyser.Protocol(protocol_name, fileaname)
    all_types = protocol.collect_atoms()
    print(all_types)

    if os.path.exists(auxinv_filename):
        aux_invs = []
        with open(auxinv_filename, 'r') as fr:
            content = list(map(lambda x: x.split(': ')[1], filter(lambda x: x, fr.read().split('\n'))))

        for line in content:
            pre = set(line.strip().split(' -> ')[0].split(' & '))
            cond = line.strip().split(' -> ')[1]
            aux_invs.append((pre, cond))
        print('read %d auxiliary invariants' % (len(aux_invs)))
    else:
        if os.path.exists(asso_filename):
            rule_tuple = []
            with open(asso_filename, 'r') as fr:
                rule_string_list = list(map(lambda x: x.split(': ')[1], filter(lambda x: x, fr.read().split('\n'))))

            for line in rule_string_list:
                pre = set(line.strip().split(' -> ')[0].split(' & '))
                cond = line.strip().split(' -> ')[1]
                rule_tuple.append((pre, cond))
            print('read %d association rules' % (len(rule_tuple)))
        else:
            replace_index = None  # if NUM == 2 else {'NODE_1': 'Home'}
            processor = preprocess.DataProcess(protocol_name, replace_index=replace_index)
            dataset, itemMeaning, para_digit = processor.execute(load=False)
            global_vars = processor.select_global(itemMeaning)
            print('global vars:', global_vars)

            learner = preprocess.RuleLearing(protocol_name, dataset, itemMeaning, global_vars=global_vars)
            rule_tuple, rule_string_list = learner.execute()
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
        # calling Murphi to remove spurious or local invariants
        selector = preprocess.SlctInv(protocol_name, [], all_types, home=False)
        _, counterex_index = selector.select_invariant(rule_string_list, num_core, '{0}/{0}.m'.format(protocol_name))

        tmp_tuple, tmp_string = copy.deepcopy(rule_tuple), copy.deepcopy(rule_string_list)
        for cex in counterex_index:
            tmp_tuple.remove(rule_tuple[cex])
            tmp_string.remove(rule_string_list[cex])
        rule_tuple, rule_string_list = tmp_tuple, tmp_string

        # instantiate invariants using symmetry expansion
        instantiator = preprocess.RuleLearing(protocol_name, [], {})
        aux_invs, aux_inv_string = instantiator.instantiate(rule_tuple, rule_string_list, all_types)

    # refine and abstract
    print_info, used_inv_string_list = protocol.refine_abstract(aux_invs, abs_type=abs_type)

    # write to abstract file
    with open(abs_filename, 'a') as fw:
        fw.write(print_info)

    # check used invariants and abstract protocol
    print('\n\n-----------------\nNo. %d' % 1)
    checker = preprocess.SlctInv(protocol_name, [], all_types, home=False)
    counterex_index = checker.check_usedF(used_inv_string_list, num_core, abs_filename)

    max_cnt = 2
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
        checker = preprocess.SlctInv(protocol_name, [], all_types, home=False)
        counterex_index = checker.check_usedF(used_inv_string_list, num_core, new_absfile)
        max_cnt += 1

    if (not counterex_index) and new_inv_tuple and new_string_list:
        print_info, used_inv_string_list = protocol.refine_abstract(new_inv_tuple, abs_type=abs_type)
        # write to abstract file
        final_absfile = "{0}/final_ABS_{0}.m".format(protocol_name)
        copyfile(fileaname, final_absfile)
        with open(final_absfile, 'a') as fw:
            fw.write(print_info)
        with open("{0}/final_aux_invs.txt".format(protocol_name), 'w') as fw:
            for i, string in enumerate(new_string_list, 1):
                fw.write('rule_{}: {}\n'.format(i, string))

        # check used invariants and abstract protocol
        checker = preprocess.SlctInv(protocol_name, [], all_types, home=False)
        counterex_index = checker.check_usedF(used_inv_string_list, num_core, abs_filename)