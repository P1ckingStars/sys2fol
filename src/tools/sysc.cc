// sysc: a spec in the language to its fol-zfc claims.
#include <fstream>
#include <iostream>
#include <sstream>

#include "src/lang/fol.h"

namespace {

std::string read(const std::string& path) {
    std::ifstream in(path);
    if (!in) throw std::runtime_error("cannot read " + path);
    std::stringstream ss;
    ss << in.rdbuf();
    return ss.str();
}

std::string stem(const std::string& path) {
    std::string base = path.substr(path.find_last_of('/') + 1);
    return base.substr(0, base.find('.'));
}

}  // namespace

int main(int argc, char** argv) {
    bool steps = false;
    std::vector<std::string> preludes, files;
    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        if (a == "--steps") steps = true;
        else if (a == "--prelude" && i + 1 < argc) preludes.push_back(argv[++i]);
        else files.push_back(a);
    }
    if (files.size() != 2) {
        std::cerr << "usage: sysc [--steps] [--prelude library.sys]... spec.sys out.fol.def\n";
        return 2;
    }
    std::string current;
    try {
        sys2fol::Program program;
        std::vector<sys2fol::Decl> forms;
        for (const std::string& p : preludes) {
            current = p;
            program.load(sys2fol::parse(p, read(p), forms));
        }
        current = files[0];
        program.load(sys2fol::parse(files[0], read(files[0]), forms));
        std::vector<std::string> trace;
        auto cs = sys2fol::claims(program, stem(files[0]), steps ? &trace : nullptr);
        std::ofstream out(files[1]);
        out << sys2fol::header(cs, files[0].substr(files[0].find_last_of('/') + 1));
        if (steps) {
            for (const std::string& t : trace) std::cout << t << "\n";
            std::cout << "\n";
            for (const auto& c : cs) std::cout << c.name << ": " << c.plain << "\n";
        }
    } catch (const sys2fol::Error& e) {
        std::cerr << current << ":" << e.pos.line << ":" << e.pos.col << ": " << e.what() << "\n";
        return 1;
    } catch (const std::exception& e) {
        std::cerr << e.what() << "\n";
        return 1;
    }
    return 0;
}
