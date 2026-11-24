// proved: every claim of each header is proved, by its fol_proof's counts: as many proved as the header has claims, none
// conditional on an unproved one, none unproved. A claim the checker dropped, its name loaded already, lowers the count.
#include <fstream>
#include <iostream>
#include <map>
#include <sstream>

#include "src/prove/formula.h"

int main(int argc, char** argv) {
    if (argc < 3 || argc % 2 == 0) {
        std::cerr << "usage: proved HEADER.fol.def TARGET.proven [HEADER.fol.def TARGET.proven]...\n";
        return 2;
    }
    auto read = [](const std::string& path) {
        std::ifstream in(path);
        if (!in) throw std::runtime_error("cannot read " + path);
        std::stringstream ss;
        ss << in.rdbuf();
        return ss.str();
    };
    try {
        bool all = true;
        for (int i = 1; i + 1 < argc; i += 2) {
            std::map<std::string, long> count;
            std::istringstream proven(read(argv[i + 1]));
            for (std::string key, value; proven >> key >> value;) count[key] = std::stol(value);
            size_t claims = sys2fol::prove::read_statements(read(argv[i]), true).size();
            bool ok = count["proved:"] == static_cast<long>(claims) && count["conditional:"] == 0 && count["unproved:"] == 0;
            std::cerr << argv[i] << ": " << (ok ? "every claim is proved: " : "FAILED: ") << count["proved:"] << " proved of "
                      << claims << " claims, " << count["conditional:"] << " conditional, " << count["unproved:"] << " unproved\n";
            all = all && ok;
        }
        return all ? 0 : 1;
    } catch (const std::exception& e) {
        std::cerr << e.what() << "\n";
        return 1;
    }
}
