#include "common.h"
#include "Repl.h"
#include "TcpNetwork.h"

DECLARE_bool(help);
DEFINE_bool(verbose, false, "Show TMET information");
DEFINE_bool(detail, false, "Show Raft information");
DEFINE_string(config, "", "Config file");
DEFINE_string(name, "", "Self name");

void setup(int argc, char **argv) {
    // Parse arguments and show help
    SetUsageMessage("Redis TMET node program");
    ParseCommandLineNonHelpFlags(&argc, &argv, true);
    if (FLAGS_help || argc != 1) {
        ShowUsageWithFlagsRestrict(argv[0], "main");
        exit(1);
    } else if (FLAGS_detail) {
        FLAGS_verbose = true;
    }

    init_prompt_color();
}

int main(int argc, char **argv) {
    setup(argc, argv);
    if (!FLAGS_config.empty()) {
        config.load(FLAGS_config);
    }
    net = new TcpNetwork();
    Repl repl;
    repl.readline();
}
