// sysrender: a spec's claims, as fol-zfc parses them, read back in the language.
#include <fstream>
#include <iostream>
#include <sstream>

#include "src/render/render.h"

namespace {

std::string read(const std::string& path) {
    std::ifstream in(path);
    if (!in) throw std::runtime_error("cannot read " + path);
    std::stringstream ss;
    ss << in.rdbuf();
    return ss.str();
}

std::string base(const std::string& path) { return path.substr(path.find_last_of('/') + 1); }

}  // namespace

int main(int argc, char** argv) {
    bool check = false;
    std::vector<std::string> preludes, files;
    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        if (a == "--check") check = true;
        else if (a == "--prelude" && i + 1 < argc) preludes.push_back(argv[++i]);
        else files.push_back(a);
    }
    if (files.empty() || files.size() > 3) {
        std::cerr << "usage: sysrender [--check] [--prelude library.sys]... spec.sys [claims.fol.def [out.sys]]\n";
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
        std::string source = read(files[0]);
        sys2fol::Source spec = sys2fol::parse(files[0], source, forms);
        program.load(spec);
        std::vector<sys2fol::render::FolClaim> claims;
        if (files.size() > 1) {
            current = files[1];
            claims = sys2fol::render::read_claims(read(files[1]));
        }
        std::string text = sys2fol::render::render(program, spec, forms, claims, files.size() > 1 ? base(files[1]) : "");
        if (files.size() == 3) std::ofstream(files[2]) << text;
        else std::cout << text;
        if (check) {
            std::string d = sys2fol::render::difference(source, text);
            if (!d.empty()) {
                std::cerr << "round trip: " << d << "\n";
                return 1;
            }
            std::cerr << "round trip: " << (files.size() > 1 ? "the claims read back as " : "the definitions print as ")
                      << base(files[0]) << "\n";
        }
    } catch (const sys2fol::Error& e) {
        // While rendering, a position is a declaration's, in the spec; a claim's error has none.
        if (files.size() > 1 && current == files[1] && e.pos.line) current = files[0];
        if (e.pos.line) current += ":" + std::to_string(e.pos.line) + ":" + std::to_string(e.pos.col);
        std::cerr << current << ": " << e.what() << "\n";
        return 1;
    } catch (const std::exception& e) {
        std::cerr << current << ": " << e.what() << "\n";
        return 1;
    }
    return 0;
}
