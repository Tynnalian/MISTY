#--------------------------------------------------------------
# Imports
#--------------------------------------------------------------

import verif_builder_lib as vb



#--------------------------------------------------------------
# Main
#--------------------------------------------------------------


"""
# Function: main()
#
# This function setups logging, parses YAML files for
# verifiaction configuration and runs test regression.
#
"""

def main():

    # Setup logging
    vb.setup_basic_logging()

    # Do all pre-run checks
    vb.pre_run_checks()

    # Parse arguments
    args = vb.get_args()

    # Check if clean only
    if args.clean is True:

        # Simply remove ouput directory
        vb.logging.info(" - Cleaning...")
        vb.run_cmd(["find {} -delete".format(args.out)], args.debug)

    # Else run regression
    else:

        # Check if sim/compile only flags are not True at the same time
        if args.sim_only is True and args.comp_only is True:
            vb.logging.fatal("--sim_only and --comp_only can't \
                be passed at the same time")
            sys.exit()

        # Check if GUI/batch modes are not True at the same time
        if args.gui is True and args.batch is True:
            vb.logging.fatal("--gui and --batch can't be passed at \
                the same time")
            sys.exit()

        # Read YAMLs
        tests = vb.read_yaml(args.testlist)
        sim = vb.read_yaml(args.rtl_sim)

        # Filter tests to obtain specific tests passed via --tests
        # If <args.tests> is None - all tests will be returned
        tests = vb.filter_yaml_entries(tests, 'test', args.tests)
        vb.check_list_empty(tests, 'No test to run!')

        # Filter sim tools
        sim = vb.filter_yaml_entries(sim, 'tool', args.tool)
        vb.check_list_empty(sim, 'No tool to run!')

        # Create output directory
        vb.run_cmd(["mkdir -p {}".format(args.out)], args.debug)
    
        # Run tests
        vb.run_tests(tests=tests, sim=sim[0], out=args.out, comp_opts=args.comp_opts, \
            sim_only=args.sim_only, comp_only=args.comp_only, sim_opts=args.sim_opts, \
                seed=args.seed, iters=args.iters, debug=args.debug, gui=args.gui, \
                    batch=args.batch, jobs=args.jobs)

        # Create regression log file
        vb.run_cmd(["mkdir -p {}".format(vb.os.path.dirname(args.rlog))], args.debug)
        vb.run_cmd(['rm -f {} && touch {}'.format(args.rlog, args.rlog)], args.debug)
        
        # Get regression results
        if args.comp_only is False:
            vb.regr_tests(tests=tests, out=args.out, seed=args.seed, iters=args.iters,
                debug=args.debug, rlog=args.rlog, rexp=args.rexp, nrexp=args.nrexp, jobs=args.jobs)


"""
# Main entry.
"""

if __name__ == '__main__':
    main() 