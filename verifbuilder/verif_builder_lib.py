"""
# Library: Verification Builder (VB) library

# Collection of functions used in Verification Builder
#
# This collection can be imported like:
#
#| import verif_builder_lib as vb
#
# Or like:
#
#| from verif_builder_lib import read_yaml
"""



#---------------------------------------------------------
# VB imports
#---------------------------------------------------------

import multiprocessing.pool
import multiprocessing
import contextlib
import subprocess
import argparse
import platform
import logging
import random
import yaml
import sys
import os



#---------------------------------------------------------
# VB variables
#---------------------------------------------------------


"""
# Variable: FNULL
#
# Global variable for suppressing output for subprocess.
"""

FNULL = open(os.devnull, 'w')


"""
# Variable: parser
#
# Global argparser variable.
"""

parser = argparse.ArgumentParser()



#---------------------------------------------------------
# VB classes
#---------------------------------------------------------


"""
# Class: VBPool
#
# Custom multiprocessing Pool class with
# no daemon processes. We use this class
# to spawn pools inside pools.
#
"""

class VBPool(multiprocessing.pool.Pool):
    def Process(self, *args, **kwds):
        proc = super(VBPool, self).Process(*args, **kwds)

        class NonDaemonProcess(proc.__class__):
            @property
            def daemon(self):
                return False

            @daemon.setter
            def daemon(self, val):
                pass

        proc.__class__ = NonDaemonProcess
        return proc



#---------------------------------------------------------
# VB main functions
#---------------------------------------------------------


"""
# Function: setup_basic_logging()
#
# This function sets basic logging format and level.
#
# Call example:
#
#| setup_basic_logging()
"""

def setup_basic_logging():
    logging.basicConfig(
        format='%(asctime)s %(levelname)-8s %(message)s',
        level=logging.INFO,
        datefmt='%Y-%m-%d %H:%M:%S'
    )


"""
# Function: pre_run_checks()
#
# This function does some pre-run checks
#
# Call example:
#
#| pre_run_checks()
"""

def pre_run_checks():
    os = platform.system()
    # We run only on Linux
    if os != 'Linux':
        logging.fatal("Wrong OS: {} (only Linux is supported)".format(os))
        sys.exit()


"""
# Function: get_argparse_args()
#
# This function returns argparse commandline arguments.
#
# Usage example:
#
#| args = get_args()
#| if args.clean is True:
#|     run_cmd(["rm -rf {}".format(args.out)])
"""

def get_args():

    # Clean flag
    parser.add_argument('--clean', action='store_true', help="Optional \
        clean flag.")
        
    # Debug switch
    parser.add_argument('--debug', action='store_true', help="Optional \
        debug flag.")

    # Jobs amount
    parser.add_argument('-j', '--jobs', type=int, default=1,
        help="Threads amount to run. Default is 1.")

    # GUI mode switch
    parser.add_argument('--gui', action='store_true', help="Optional \
        GUI mode flag. If passed - simulation will be started with \
        flag which was stated in 'gui' field in RTL simulation YAML ( \
        see --rtl_sim).")

    # Batch mode switch
    parser.add_argument('--batch', action='store_true', help="Optional \
        batch mode flag. If passed - simulation will be started with \
        flag which was stated in 'batch' field in RTL simulation YAML ( \
        see --rtl_sim).")

    # Compile only switch
    parser.add_argument('--comp_only', action='store_true', help="Optional \
        compilation only flag. If passed - only compilation will be executed \
            from RTL simulation YAML (see --rtl_sim)")

    # Simulate only switch
    parser.add_argument('--sim_only', action='store_true', help="Optional \
        simulation only flag. If passed - only simulation will be executed \
            from RTL simulation YAML (see --rtl_sim)")

    # Output directory
    parser.add_argument('--out', default='./out', help="Output directory.")

    # Tool for compilation and simulation
    parser.add_argument('--tool', required=True,
        help="Tool for compilation and simulation (see --rtl_sim).")

    # Simulation seed
    parser.add_argument('--seed', type=int,
        default=random.randrange(pow(2,32)-1),
            help="Simulation seed, if not passed - random from 0 to 2^32-1).")

    # Testlist with test scenarios
    parser.add_argument('--testlist', default=None, help= "YAML testlist with \
        test scenarios.")

    # RTL compilation and simulation commands YAML
    parser.add_argument('--rtl_sim',  default='./rtl_simulation.yaml',
        help="RTL compilation and simulation commands YAML.")

    # Aargument for test scenarios to run
    parser.add_argument('--tests', nargs='+', default=None,
        help="Tests from RTL simulation YAML, if not passed - all tests will \
            be simulated.")

    # Amount for each test
    parser.add_argument('--iters', default=None,
        help="Iterations for each test (overrrides <iterations> from YAML \
            testlist).")
    
    # Regression log path
    parser.add_argument('--rlog', default='./out/regr.log', help="Regression \
        log path")

    # Strings list to determine if test was passed
    parser.add_argument('--rexp', nargs='+', default=['UVM_ERROR :    0',
        'UVM_FATAL :    0'], help="Strings which must be found inside \
            simulation directory for each test to make decision that this test \
                is passed")
    
    # Strings list to determine if test was passed
    parser.add_argument('--nrexp', nargs='+', default=[],
            help="Strings which must NOT be found inside simulation directory \
                for each test to make decision that this test is passed")

    # Configuration of RTL design to verify (YAML)
    parser.add_argument('--config', default=None, help="RTL design config \
        file. Contains defines, parameters and etc.")

    # Additional compilation options
    parser.add_argument('--comp_opts', default='', help="Additional \
        compilation options. Will be added to the compilation commands \
            in RTL simulation YAML (see --rtl_sim).")

    # Additional simulation options
    parser.add_argument('--sim_opts', default='', help="Additional \
        simulation options. Will be added to the simulation commands \
            in RTL simulation YAML (see --rtl_sim).")

    args = parser.parse_args()

    return args


"""
# Function: none_to_str(data)
#
# If <data> is None - returns '', else returns <data>
"""

def none_to_str(data):
    if data is None:
        return ''
    else:
        return data


"""
# Function: replace_in_str_list(target: list, what: str, on: str)
#
# This function replaces every <what> on <on> in every entry in
# <target> list. If <on> is None - replaces <what> on ''.
#
# Usage example:
#
#| cmp = sim['compile']['cmd']
#| cmp = replace_in_str_list(cmp, '<out>', out)
"""

def replace_in_str_list(target: list, what: str, on: str):
    target = [entry.replace(what, none_to_str(on)) for entry in target]
    return target


"""
# Function: read_yaml(path: str)
#
# This function reads YAML from <path> via safe load
# and returns result. Prints exception if something
# went wrong.
#
# Usage example:
#
#| cmp = sim['compile']['cmd']
#| cmp = replace_in_str_list(cmp, '<out>', out)
"""

def read_yaml(path: str):
    with open(path, "r") as f:
        try:
            logging.info("Reading {}".format(path))
            data = yaml.safe_load(f)
        except yaml.YAMLError as exc:
            print(exc)
    return data


"""
# Function: filter_yaml_entries(yaml_entries: dict, exp: str, req: list)
#
# This function filters <yaml_entries> by <req>
# for entry in <yaml_entries>:
#     if(entry[<exp>] in <req>):
#         result.append(entry)
#
# Usage example:
#
#| # Filters from tests only entries with entry['test'] is 'basic_test'
#| # or 'common_test"
#| tests = filter_yaml_entries(tests, 'test', ['basic_test', 'common_test'])
"""

def filter_yaml_entries(yaml_entries: dict, exp: str, req: list):
    result = []
    if(req is None):
        result = yaml_entries
    else:
        for entry in yaml_entries:
            if(entry[exp] in req):
                result.append(entry)
    logging.info("Obtained entries:")
    for entry in result:
        logging.info(" - [{}]".format(entry[exp]))
    return result


"""
# Function: check_list_empty(data: str, err: str):
#
# Checks if <data> is empty. If yes - throws an
# error and calls sys.exit().
#
# Usage example:
#
#| sim = vb.filter_yaml_entries(sim, 'tool', args.tool)
#| vb.check_list_empty(sim, 'No tool to run!')
"""

def check_list_empty(data: str, err: str):
    if data == []:
        logging.error(err)
        sys.exit()


"""
# Function: run_tests(**kwargs)
#
# This function runs test regression. For test in
# kwargs['tests'] calls run_test(kwargs + test).
# Takes in keyword arguments for ease of modification
#
# Supported arguments for now:
# 
# jobs      - Threads amount to run
# sim       - RTL simulation YAML entry
# tests     - YAML testlist entry
# out       - Output result directory
# iters     - Iterations amount
# seed      - Simulation seed
# comp_opts - Additional compilation options
# sim_opts  - Additional simulation options
# comp_only - Compilation only flag
# sim_only  - Simulation only flag
# gui       - GUI mode flag
# batch     - Batch mode flag
#
# Usage example:
#
#| # Read YAMLs
#| tests = read_yaml(args.testlist)
#| sim = read_yaml(args.rtl_sim)
#| # Filter tests
#| tests = process_entries(tests, 'test', args.tests)
#| # Filter sim tools
#| sim = process_entries(sim, 'tool', args.tool)
#| # Create output directory
#| run_cmd(["mkdir -p {}".format(args.out)])
#| # Run tests
#| run_tests(tests=tests, sim=sim[0], out=args.out,
#|     seed=args.seed, iters=args.iters, jobs=args.jobs)
"""

def run_tests(**kwargs):
    logging.info("Running tests:")
    pool = VBPool(kwargs['jobs'])
    args = []
    for test in kwargs['tests']:
        args.append(dict(kwargs, test=test))
    fp = [(pool.apply_async(run_test, kwds=arg), arg) for arg in args]
    for f, p in fp:
        r = f.get()
    pool.close()
    pool.join()


"""
# Function: run_test(**kwargs)
#
# This function does test compilation and simulation for
# kwargs['test'] YAML testlist entry.
# Runs compile_test(kwargs) and after that runs
# sim_test(kwargs + iter) kwargs['iters'] times
#
# Supported arguments for now:
# 
# jobs      - Threads amount to run
# sim       - RTL simulation YAML entry
# test      - YAML testlist entry
# out       - Output result directory
# iters     - Iterations amount
# seed      - Simulation seed
# comp_opts - Additional compilation options
# sim_opts  - Additional simulation options
# comp_only - Compilation only flag
# sim_only  - Simulation only flag
# gui       - GUI mode flag
# batch     - Batch mode flag
#
# Usage example:
#
#| for test in kwargs['tests']:
#|     logging.info("Running '{}'...".format(test['test']))
#|     run_test(test=test, **kwargs)
"""

def run_test(**kwargs):
    # Get iterations
    if kwargs['iters'] is None:
        iters = kwargs['test']['iterations']
    else:
        iters = kwargs['iters']
    if kwargs['sim_only'] is False:
        compile_test(**dict(kwargs))
    if kwargs['comp_only'] is False:
        pool = multiprocessing.Pool(kwargs['jobs'])
        args = []
        for iter in range(int(iters)):
            kwargs['seed'] = str(int(kwargs['seed']) + iter)
            args.append(dict(kwargs, iter=iter))
        fp = [(pool.apply_async(sim_test, kwds=arg), arg) for arg in args]
        for f, p in fp:
            r = f.get()
        pool.close()
        pool.join()


"""
# Function: compile_test(**kwargs)
#
# Main function for running test compilation commands.
# Takes in keyword arguments for ease of modification.
#
# Supported arguments for now:
# 
# sim       - RTL simulation YAML entry
# test      - YAML testlist entry
# out       - Output result directory
# comp_opts - Additional compilation options
#
# Usage example:
#
#| sim = read_yaml(args.rtl_sim)
#| tests = process_entries(tests, 'test', args.tests)
#| sims = process_entries(sim, 'tool', args.tool)
#| compile_test(sim=sims[0], test=tests[0], out=args.out)
"""

def compile_test(**kwargs):
    # Print info
    logging.info(" - [{}] Compiling...".format(kwargs['test']['test']))
    # Obtain arguments
    sim  = kwargs['sim'      ]
    test = kwargs['test'     ]
    out  = kwargs['out'      ]
    opts = kwargs['comp_opts'] + ' ' + none_to_str(test['comp_opts'])
    # Get compilation commands
    cmp_cmd = sim['compile']['cmd']
    # Form compilation directory path
    cmp_dir = out + '/' + test['test']
    # Replace specific fields
    cmp_cmd = replace_in_str_list(cmp_cmd, '<comp_opts>', opts)
    cmp_cmd = replace_in_str_list(cmp_cmd, '<cmp_dir>', cmp_dir)
    cmp_cmd = replace_in_str_list(cmp_cmd, '<out>', out)
    cmp_cmd = replace_in_str_list(cmp_cmd, '\n', '')
    # Create compilation directory
    run_cmd(["mkdir -p {}".format(cmp_dir)], kwargs['debug'])
    # Compile
    run_cmd(cmp_cmd, kwargs['debug'])


"""
# Function: sim_test(**kwargs)
#
# Main function for running test simulation commands.
# Takes in keyword arguments for ease of modification.
#
# Supported arguments for now:
# 
# sim       - RTL simulation YAML entry
# test      - YAML testlist entry
# out       - Output result directory
# iter      - Iteration number
# seed      - Simulation seed
# sim_opts  - Additional simulation options
# gui       - GUI mode flag
# batch     - Batch mode flag
#
# Usage example:
#
#| for i in range(10):
#|     logging.info(" - Simulating iteration {}...".format(iter))
#|     sim_test(sim=..., test=..., iter=i, out='out/',
#|         seed=random.randrange(pow(2,32)-1))
"""

# Run single test
def sim_test(**kwargs):
    # Print info
    logging.info(" - [{}] Simulating iteration {}...".format( \
        kwargs['test']['test'], kwargs['iter']))
    # Obtain arguments
    sim   = kwargs['sim' ]
    test  = kwargs['test']
    out   = kwargs['out' ]
    iter  = kwargs['iter']
    seed  = kwargs['seed']
    opts  = kwargs['sim_opts'] + ' ' + none_to_str(test['sim_opts'])
    gui   = kwargs['gui']
    batch = kwargs['batch']
    # Get simulation commands
    sim_cmd = sim['sim']['cmd']
    # Form compilation directory path
    cmp_dir = out + '/' + test['test']
    # Form simulation directory path
    sim_dir = out + '/' + test['test'] + '/' + \
        test['test'] + '_' + str(iter) + '_' + str(seed)
    # Replace specific fields
    sim_cmd = replace_in_str_list(sim_cmd, '<cov_opts>', test['cov_opts'])
    sim_cmd = replace_in_str_list(sim_cmd, '<sim_dir>', sim_dir)
    sim_cmd = replace_in_str_list(sim_cmd, '<cmp_dir>', cmp_dir)
    sim_cmd = replace_in_str_list(sim_cmd, '<out>', out)
    sim_cmd = replace_in_str_list(sim_cmd, '<seed>', str(seed))
    sim_cmd = replace_in_str_list(sim_cmd, '<rtl_test>', test['rtl_test'])
    sim_cmd = replace_in_str_list(sim_cmd, '<sim_opts>', opts)
    sim_cmd = replace_in_str_list(sim_cmd, '\n', '')
    # Apply GUI or batch mode
    sim_cmd = apply_mode(sim, sim_cmd, gui, batch)
    # Create simulation directory
    run_cmd(["mkdir -p {}".format(sim_dir)], kwargs['debug'])
    # Simulate
    run_cmd(sim_cmd, kwargs['debug'])


"""
# Function: apply_mode(sim: dict, cmds: list)
#
# This functions applies GUI or batch mode
# to <sim_cmd> simulation commands. It gets
# GUI and batch simulator specific flags and
# replaces '<mode>' in every command in <sim_cmd>
# with appropriate flag. Function also deletes
# GUI flag from <sim_cmd> if batch mode is
# chosen and vice versa, as well as removes
# '<mode>' from <sim_cmd> if it was not removed
# by modes apply.
#
# Supported arguments for now:
#
# sim     - RTL simulation YAML entry
# sim_cmd - Simulation commands list
# gui     - GUI mode flag
# batch   - Batch mode flag
#
# Usage example:
#
#| sim     = kwargs['sim']
#| sim_cmd = sim['sim']['cmd']
#| apply_mode(sim, sim_cmd, 1, 0)
"""
def apply_mode(sim: dict, sim_cmd: list, gui: bool, batch: bool):
    # If GUI mode flag was passed
    if gui is True:
        try:
            gui_flag = sim['sim']['gui']
            sim_cmd = replace_in_str_list(sim_cmd, '<mode>', gui_flag)
        except KeyError:
            logging.warning("'gui' field was not found in RTL YAML")
        try:
            batch_flag = sim['sim']['batch']
            sim_cmd = replace_in_str_list(sim_cmd, ' ' + batch_flag + ' ', ' ')
        except KeyError:
            pass
    # If batch mode flag was passed
    if batch is True:
        try:
            batch_flag = sim['sim']['batch']
            sim_cmd = replace_in_str_list(sim_cmd, '<mode>', batch_flag)
        except KeyError:
            logging.warning("'batch' field was not found in RTL YAML")
        try:
            gui_flag = sim['sim']['gui']
            sim_cmd = replace_in_str_list(sim_cmd, ' ' + gui_flag + ' ', ' ')
        except KeyError:
            pass
    # If <mode> was not removed by mode flags, we
    # must remove it manually
    sim_cmd = replace_in_str_list(sim_cmd, '<mode>', '')
    return sim_cmd


"""
# Function: regr_tests(**kwargs)
#
# This function does test regression check. For test in
# kwargs['tests'] calls regr_test(kwargs + test).
# After all tests were processed, checks kwargs['rlog']
# file and write conclusion to it with passed/failed tests
# amount.
# Takes in keyword arguments for ease of modification.
#
# Supported arguments for now:
# 
# jobs  - Threads amount to run
# tests - YAML testlist entries
# out   - Output result directory
# iters - Iterations amount
# seed  - Simulation seed
# rlog  - Regression log file path
# rexp  - List of expressions to be present for test pass
# nrexp - List of expressions NOT to be present for test pass
#
# Usage example:
#
#| # Read YAMLs
#| tests = read_yaml(args.testlist)
#| sim = read_yaml(args.rtl_sim)
#| # Filter tests to obtain specific tests passed via --tests
#| # If <tests> is None - all tests will be returned
#| tests = filter_yaml_entries(tests, 'test', args.tests)
#| # Filter sim tools
#| # Only first tool wll be chosen
#| sim = filter_yaml_entries(sim, 'tool', args.tool)[0]
#| # Create regression log file
#| run_cmd(["mkdir -p {}".format(os.path.dirname(args.rlog))], args.debug)
#| run_cmd(['rm -f {} && touch {}'.format(args.rlog, args.rlog)], args.debug)
#| # Get regression results
#| vb.regr_tests(tests=tests, out=args.out, seed=args.seed, iters=args.iters,
#|     debug=args.debug, rlog=args.rlog, rexp=args.rexp, nrexp=args.nrexp, jobs=args.jobs)
"""

def regr_tests(**kwargs):
    # Run checking
    logging.info('Checking regression result:')
    # Check for available tests
    if kwargs['tests'] == []:
        logging.error('No test to check!')
    # Check test result
    pool = multiprocessing.Pool(kwargs['jobs'])
    args = []
    for test in kwargs['tests']:
        args.append(dict(kwargs, test=test))
    fp = [(pool.apply_async(regr_test, kwds=arg), arg) for arg in args]
    for f, p in fp:
        r = f.get()
    pool.close()
    pool.join()
    # Open regression log
    rlog = open(kwargs['rlog'], 'r')
    # Check for 'PASSED' in each line
    passed = 0; failed = 0
    for result in rlog.readlines():
        if 'PASSED' in result: passed += 1
        elif 'FAILED' in result : failed += 1
    rlog.close()
    # Print passed and failed
    with open(kwargs['rlog'], 'a') as rlog:
        rlog.write('PASSED: {} FAILED: {}'.format(passed, failed))
    # Print regression result to the console
    logging.info('Regression result at {}'.format(kwargs['rlog']))
    logging.info('PASSED: {} FAILED: {}'.format(passed, failed))


"""
# Function: regr_test(**kwargs)
#
# This function does test result check for kwargs['test']
# YAML testlist entry.
# Runs regr_test_log(kwargs + iter) kwargs['iters'] times.
# For each test write its name, simulation directory and
# result to kwargs['rlog'] file.
# Takes in keyword arguments for ease of modification.
#
# Supported arguments for now:
# 
# test  - YAML testlist entry
# out   - Output result directory
# iters - Iterations amount
# seed  - Simulation seed
# rlog  - Regression log file path
# rexp  - List of expressions to be present for test pass
# nrexp - List of expressions NOT to be present for test pass
#
# Usage example:
#
#| for test in kwargs['tests']:
#|     logging.info(" - Checking '{}'...".format(test['test']))
#|     regr_test(**dict(kwargs, test=test))
"""

def regr_test(**kwargs):
    # Print info
    logging.info(" - [{}] Checking...".format(kwargs['test']['test']))
    # Get iterations
    if kwargs['iters'] is None:
        iters = kwargs['test']['iterations']
    else:
        iters = kwargs['iters']
    # Open regression log file and write test result to it
    with open(kwargs['rlog'], 'a') as rlog:
        for iter in range(int(iters)):
            # Increment seed
            kwargs['seed'] = str(int(kwargs['seed']) + iter)
            # Process test log
            [test, sim_dir, passed, info] = regr_test_log(**dict(kwargs, iter=iter))
            # Write result to log file
            if passed is True:
                rlog.write('\n---\n[{}] {}: PASSED {}\n---\n'.format(test, sim_dir, info))
            else:
                rlog.write('\n---\n[{}] {}: FAILED {}\n---\n'.format(test, sim_dir, info))


"""
# Function: regr_test_log(**kwargs)
#
# This function checks simulation directory for kwargs['rexp']
# and kwargs['nrexp'] expressions. If all kwargs['rexp']
# expressions were found in this directory and all kwargs['nrexp']
# expressions was not found <test_pass> will be True, else False.
# Returns test name, simulation directory, <test_pass> variables
# as list, and <test_info> as additional test pass/fail info.
# Takes in keyword arguments for ease of modification.
#
# Supported arguments for now:
# 
# test  - YAML testlist entry
# out   - Output result directory
# iter  - Iteration number
# seed  - Simulation seed
# rexp  - List of expressions to be present for test pass
# nrexp - List of expressions NOT to be present for test pass
#
# Usage example:
#
#| for iter in range(int(iters)):
#|     logging.info(" - Checking iteration {}...".format(iter))
#|     # Increment seed
#|     kwargs['seed'] = str(int(kwargs['seed']) + iter)
#|     # Process test log
#|     [test, sim_dir, passed, info] = regr_test_log(**dict(kwargs, iter=iter))
"""

def regr_test_log(**kwargs):
    # Obtain arguments
    test = kwargs['test']
    out  = kwargs['out' ]
    iter = kwargs['iter']
    seed = kwargs['seed']
    rexp = kwargs['rexp']
    nrexp = kwargs['nrexp']
    # Form simulation directory path
    sim_dir = out + '/' + test['test'] + '/' + \
        test['test'] + '_' + str(iter) + '_' + str(seed)
    # Additional info about test pass/fail
    test_info = ''
    # For each expression find if it's inside simulation directory
    test_pass = True
    for exp in rexp:
        test_res = grep_sim_results(sim_dir, exp, kwargs['debug'])
        # Final result is True if all expressions are inside
        test_pass = test_pass and ( test_res != '' )
        if not test_pass:
            test_info += '\n' + 'Expected (--rexp) string was not found: "' + exp + '"'
            break
    if test_pass:
        for exp in nrexp:
            test_res = grep_sim_results(sim_dir, exp, kwargs['debug'])
            # Final result is True if all expressions are NOT inside
            test_pass = test_pass and ( test_res == '' )
            if not test_pass:
                test_info += '\n' + 'Not expected (--nrexp) string was found:\n' + test_res
    # Return result with simulation directory and test name
    return [test['test'], sim_dir, test_pass, test_info]


"""
# Function: grep_sim_results(sim_dir: str, exp: str, debug: bool)
#
# Usage example:
#
#| test_res = grep_sim_results('./out/base_test', 'UVM_ERROR :    0', False)
"""

def grep_sim_results(sim_dir: str, exp: str, debug: bool = True):
    out = run_cmd(['grep -r {} -e "{}"'.format(sim_dir, exp)], debug)
    return out


"""
# Function: run_cmd(cmds: list, debug: bool)
#
# Function for running every command in <cmds>
# via subprocess.run(). If <debug> is True -
# output will be forwarded to console, else
# output will be suppressed. Returns the last
# command stdout as string.
#
#
# Usage example:
#
#| run_cmd(["mkdir -p {}".format('out/')])
"""

def run_cmd(cmds: list, debug: bool = True):
    for cmd in cmds:
        p = subprocess.run(cmd, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, shell=True)
        out = p.stdout.decode('utf-8')
        if debug is True:
            print(out)
        # We expecting non-zero return not empty output to throw exception
        if ( p.returncode != 0 ) and ( out != '' ):
            raise Exception("Error while executing command: {} \n".format(cmd) + \
                "Output message: {}".format(out))
    return out
