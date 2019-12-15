import os
import sys
import copy
import argparse
from shutil import copyfile
from collections import OrderedDict
from murphi_analysis.call_murphi import run_murphi
from preprocess_opts.preprocess import pre_checker
from preprocess_opts.preprocess import DataProcess
from association_rule_learning.learn import RuleLearing
from association_rule_learning.learn import split_string_to_tuple
from murphi_analysis.analyser import Protocol
from association_rule_learning.select_invs import SlctInv


def pre(data_dir, protocol_name, node_num, murphi_url):
    def return_replace_index():
        od = OrderedDict()
        od['NODE_1'] = 'Home'
        od['NODE_2'] = 'NODE_1'
        od['NODE_3'] = 'NODE_2'
        return od

    if not os.path.exists('{1}/{0}/{0}.txt'.format(protocol_name, data_dir)):
        run_murphi(data_dir, protocol_name, murphi_dir=murphi_url,
                   aux_para='-ta >{0}/{1}/{1}.txt'.format(data_dir, protocol_name))

    replace_index = None if node_num == 2 else return_replace_index()
    processor = DataProcess(data_dir, protocol_name, replace_index=replace_index)
    dataset, itemMeaning, para_digit = processor.execute(load=True)
    global_vars = processor.select_global(itemMeaning)

    prot_analyzer = Protocol(data_dir, protocol_name, '{0}/{1}/{1}.m'.format(data_dir, protocol_name))
    all_types = prot_analyzer.collect_atoms()

    return dataset, itemMeaning, global_vars, all_types


def learn(data_dir, protocol_name, dataset, itemMeaning, global_vars, kmax):
    learner = RuleLearing(data_dir, protocol_name, dataset, itemMeaning, global_vars=global_vars, max_freq_size=kmax,
                          min_support=0.0, min_confidence=1.0)
    rule_tuple, rule_string_list = learner.execute()
    assert len(rule_tuple) == len(rule_string_list)
    return rule_tuple, rule_string_list


def select(data_dir, protocol_name, abs_type, home_flag, num_core, rule_tuple, rule_string_list, prot_analyzer,
           all_types=None):
    # prot_analyzer = Protocol(data_dir, protocol_name, '{0}/{1}/{1}.m'.format(data_dir, protocol_name))
    if all_types is None:
        all_types = prot_analyzer.collect_atoms()

    instantiator = RuleLearing(data_dir, protocol_name, [], {})
    instan_rule_tuple, _ = instantiator.instantiate(rule_tuple, rule_string_list, all_types)
    _, candidate_inv_string = prot_analyzer.refine_abstract(instan_rule_tuple, abs_type=abs_type,
                                                            print_usedinvs_to_file=False, boundary_K=1)
    candidate_inv_string = list(set(candidate_inv_string))
    candidate_inv_tuple = list(map(lambda x: split_string_to_tuple(x), candidate_inv_string))
    assert len(candidate_inv_string) == len(candidate_inv_tuple)
    print('select candidate association rules: before: {}, after: {}'.format(len(instan_rule_tuple),
                                                                             len(candidate_inv_tuple)))

    with open('{}/{}/candidate_rules.txt'.format(data_dir, protocol_name), 'w') as f:
        for cnt, stmt in enumerate(sorted(candidate_inv_string, key=lambda x: len(x)), 1):
            f.write('rule_%d: %s\n' % (cnt, stmt))

    # minimize candidate invs, because runnign murphi costs lots of time
    minimzer = RuleLearing(data_dir, protocol_name, [], {})
    rule_tuple, rule_string_list = minimzer.symmetry_reduction(candidate_inv_tuple, candidate_inv_string,
                                                               all_types)
    # remove spurious invariants
    # start removing spurious invariants
    selector = SlctInv(data_dir, protocol_name, [], all_types, home=home_flag)
    _, counterex_index = selector.select_invariant(rule_string_list, keep_file=False, num_core=num_core,
                                                   original_file='{0}/{1}/{1}.m'.format(data_dir, protocol_name),
                                                   aux_para="-finderrors -ndl")

    tmp_tuple, tmp_string = copy.deepcopy(rule_tuple), copy.deepcopy(rule_string_list)
    for cex in counterex_index:
        tmp_tuple.remove(rule_tuple[cex])
        tmp_string.remove(rule_string_list[cex])
    rule_tuple, rule_string_list = tmp_tuple, tmp_string

    # instantiate invariants using symmetry expansion
    instantiator = RuleLearing(data_dir, protocol_name, [], {})
    aux_invs, aux_inv_string = instantiator.instantiate(rule_tuple, rule_string_list, all_types)
    return aux_invs, aux_inv_string


def cmp(data_dir, args, all_types, aux_invs, abs_filename, prot_analyzer):
    home_flag = False if args.node_num < 3 else True

    print_info, used_inv_string_list = prot_analyzer.refine_abstract(aux_invs, abs_type=args.abs_obj,
                                                                     print_usedinvs_to_file=True,
                                                                     boundary_K=args.kmax)
    with open(abs_filename, 'a') as fw:
        fw.write(print_info)

    checker = SlctInv(data_dir, args.protocol, [], all_types, home=home_flag)
    counterex_index = checker.check_usedF(used_inv_string_list, 1, abs_filename,
                                          aux_para="-finderrors -ndl -m100",
                                          keep_file=True)
    return counterex_index, used_inv_string_list


def iter_cmp(data_dir, args, all_types=None, aux_invs=None, abs_filename=None, prot_analyzer=None, max_cnt=10):
    home_flag = False if args.node_num < 3 else True

    prot_dir = '{}/{}.m'.format(data_dir, args.protocol)
    counterex_index, used_inv_string_list = cmp(data_dir, args, all_types, aux_invs,
                                                abs_filename,
                                                prot_analyzer)
    if counterex_index:
        # if still exists counterexample after strengthening,
        # then iterate until max_cnt or no counterexample
        print('\n\n-----------------\nCounter example founded! Start iteration.\n')
        new_inv_tuple, new_string_list = [], []
        cnt = 1

        while counterex_index and cnt < max_cnt:
            # print('\n\n-----------------\nNo. %d' % max_cnt)
            # with open(used_aux_invs, 'a') as fw:
            #     fw.write('\n\n-----------------\nNo. %d\n' % max_cnt)

            tmp_string = copy.deepcopy(used_inv_string_list)
            for cex in counterex_index:
                tmp_string.remove(used_inv_string_list[cex])
            new_string_list = tmp_string
            new_inv_tuple = list(map(lambda x: split_string_to_tuple(x), new_string_list))

            new_absfile = "{2}/{0}/ABS_{0}_{1}.m".format(args.protocol, cnt, data_dir)
            copyfile(prot_dir, new_absfile)

            print_info, used_inv_string_list = prot_analyzer.refine_abstract(new_inv_tuple, abs_type=args.abs_obj,
                                                                             print_usedinvs_to_file=True, boundary_K=1)
            with open(new_absfile, 'a') as fw:
                fw.write(print_info)
            checker = SlctInv(data_dir, args.protocol, [], all_types, home=home_flag)
            counterex_index = checker.check_usedF(used_inv_string_list, 1, new_absfile,
                                                  "-finderrors -ndl -m100",
                                                  keep_file=True)
            cnt += 1
        if counterex_index:
            print('\nCounter-examples:{}\n'.format(counterex_index))
    else:
        print('End verifing, no counter-examples')


def all(data_dir, args, murphi_url, max_cnt=10, end_with='all', abs_filename=None):
    home_flag = False if args.node_num < 3 else True
    print('{}\nPreprocessing'.format('*' * 30))
    dataset, itemMeaning, global_vars, all_types = pre(data_dir, args.protocol, args.node_num, murphi_url)
    if end_with == 'pre': return

    print('{}\nLearning'.format('*' * 3))
    rule_tuple, rule_string_list = learn(data_dir, args.protocol, dataset, itemMeaning, global_vars, args.kmax)
    if end_with == 'learn': return

    print('{}\nSelecting'.format('*' * 30))
    prot_analyzer = Protocol(data_dir, args.protocol, '{0}/{1}/{1}.m'.format(data_dir, args.protocol))
    aux_invs, aux_inv_string = select(data_dir, args.protocol, args.abs_obj, home_flag, 1, rule_tuple,
                                      rule_string_list, prot_analyzer, all_types)

    print('{}\nStrenghening and abstracting'.format('*' * 30))
    abs_filename = "{1}/{0}/ABS_{0}.m".format(args.protocol, data_dir) if abs_filename is None else abs_filename
    iter_cmp(data_dir, args, all_types, aux_invs, abs_filename, prot_analyzer, max_cnt=max_cnt)


def main(arguments):
    parser = argparse.ArgumentParser(
        description='{0}\n{1}\n{0}\n'.format('*' * 15, 'Learning-based CMP (L-CMP)'),
        formatter_class=argparse.ArgumentDefaultsHelpFormatter)
    group = parser.add_mutually_exclusive_group()
    group.add_argument('-all', '--all', help="\'all\': go through all options in L-CMP", action="store_true")
    group.add_argument('-pre', '--preprocess', help="\'preprocess\': calculate reachable set only", action="store_true")
    group.add_argument('-l', '--learn', help="\'learn\': learn auxiliary invariants only", action="store_true")
    group.add_argument('-cmp', '--cmp', help="\'cmp\': conduct cmp only", action="store_true")
    # group.add_argument('-str', '--strengh', help="\'cmp\': strengthen the protocol only", action="store_true")
    # group.add_argument('-sa', '--refineabstract', help="\'cmp\': abstract the protocol only", action="store_true")

    parser.add_argument('-p', '--protocol', help="Name of the protocol under verification.",
                        type=str, required=True)
    parser.add_argument('-a', '--abs_obj', help="Object under abstraction",
                        type=str, default='NODE')
    parser.add_argument('-n', '--node_num', help="Number of normal nodes", type=int, default=2)
    parser.add_argument('-k', '--kmax', help="Max size of frequent itemset", type=int, default=3)
    parser.add_argument('-s', '--support', help="Minimum support threshold", type=float, default=0.0)
    parser.add_argument('-c', '--confidence', help="Minimum confidence threshold", type=float, default=1.0)
    parser.add_argument('-i', '--iter', help="Max iteration of strengthening", type=int, default=2)
    parser.add_argument('-src', '--srcfile', help="Path to the protocol under verification.", type=str)
    parser.add_argument('-out', '--outputfile', help="Path to the destination protocol.", type=str)

    args = parser.parse_args(arguments)
    print(args)

    murphi_url = pre_checker(data_dir='./protocols/', prot_name=args.protocol, murphi_dir='./murphi_url.txt')

    data_dir = './protocols'
    if args.all or args.cmp:
        all(data_dir, args, murphi_url)
    elif args.preprocess:
        all(data_dir, args, murphi_url,end_with='pre')
    elif args.learn:
        all(data_dir, args, murphi_url, end_with='learn')


    # elif args.learn:

    # elif args.cmp:
    #     home_flag = False if args.node_num < 3 else True
    #     iter_cmp(data_dir, args.protocol, args.abs_obj, args.kmax, home_flag, all_types, aux_invs, abs_filename,
    #              prot_analyzer,
    #              max_cnt=10)


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
