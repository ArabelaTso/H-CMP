import re
import os
import sys
import copy
import subprocess
from collections import OrderedDict

import analyser as analyser
import preprocess as preprocess


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


def extract_formulas(stmt):
    if not stmt:
        sys.stderr.write('Empty input!')
        sys.exit()
    else:
        if re.match(r'!\s?\((.*?)\)', stmt):
            part = re.findall(r'!\s?\((.*?)\)', stmt)
            formulas = re.split(r"\s?&\s?", part[0])
            kmax = len(formulas)
            #
            # added_formulas = []
            # for formula in formulas:
            #     if re.findall(r'\btrue\b', formula):
            #         added_formulas.append(re.sub(r'\btrue\b', 'false', formula))
            #     elif re.findall(r'\bfalse\b', formula):
            #         added_formulas.append(re.sub(r'\bfalse\b', 'true', formula))

            # formulas.extend(added_formulas)
            print('\natomic formulas: {}\nKmax = {}\n'.format(formulas, kmax))
            return set(formulas), kmax
        else:
            sys.stderr.write('Empty input!')
            sys.exit()


def decide_stmt(protocol_name, atom_formulas, kmax):
    # calculate reachable set
    if not os.path.exists("{0}/{0}.txt".format(protocol_name)):
        run_murphi('{0}/{0}.m'.format(protocol_name), '-ta >{0}/{0}.txt'.format(protocol_name))

    # define configurations
    abs_type = 'NODE'
    NODE_NUM, set_n, min_support, min_config, num_core = 2, 3, 0.0, 1.0, 1
    home_flag = (NODE_NUM != 2)

    fileaname = "{0}/{0}.m".format(protocol_name)
    protocol_analyser = analyser.Protocol(protocol_name, fileaname)
    all_types = protocol_analyser.collect_atoms()

    od = OrderedDict()
    od['NODE_1'] = 'Home'
    od['NODE_2'] = 'NODE_1'
    od['NODE_3'] = 'NODE_2'
    replace_index = None if NODE_NUM == 2 else od

    # preprocess
    processor = preprocess.DataProcess(protocol_name, replace_index=replace_index, atom_formulas=atom_formulas,
                                       has_atom=True)
    dataset, itemMeaning, para_digit = processor.execute(load=False)

    # select global variables from protocol description
    global_vars = processor.select_global(itemMeaning)
    print('global vars:', global_vars)

    # learning association rules
    learner = preprocess.RuleLearing(protocol_name, dataset, itemMeaning, global_vars=global_vars,
                                     max_freq_size=kmax)
    rule_tuple, rule_string_list = learner.execute()
    assert len(rule_tuple) == len(rule_string_list)
    #
    # # minimize candidate invs
    # minimzer = preprocess.RuleLearing(protocol_name, [], {})
    # rule_tuple, rule_string_list = minimzer.symmetry_reduction(rule_tuple, rule_string_list,
    #                                                            all_types)

    # remove spurious invariants
    selector = preprocess.SlctInv(protocol_name, [], all_types, home=home_flag)
    _, counterex_index = selector.select_invariant(rule_string_list, num_core,
                                                   '{0}/{0}.m'.format(protocol_name),
                                                   aux_para="-finderrors -ndl")

    tmp_tuple, tmp_string = copy.deepcopy(rule_tuple), copy.deepcopy(rule_string_list)
    for cex in counterex_index:
        tmp_tuple.remove(rule_tuple[cex])
        tmp_string.remove(rule_string_list[cex])
    rule_tuple, rule_string_list = tmp_tuple, tmp_string

    # instantiate invariants using symmetry expansion
    instantiator = preprocess.RuleLearing(protocol_name, [], {})
    aux_invs, aux_inv_string = instantiator.instantiate(rule_tuple, rule_string_list, all_types)
    return aux_invs, aux_inv_string

if __name__ == "__main__":
    protocol_name = 'mutualEx'
    stmt = '!(n[NODE_1] = C & x = true & n[NODE_2] = C)'
    # stmt = '!(n[1] = C & x = true & n[2] = C)'

    # protocol_name = 'german'
    # stmt = '!(Chan2[NODE_1].Cmd = GntE & Chan2[NODE_1].Data = AuxData)'
    formulas, kmax = extract_formulas(stmt)
    _, aux_inv_string = decide_stmt(protocol_name, formulas, kmax)
    print(aux_inv_string)