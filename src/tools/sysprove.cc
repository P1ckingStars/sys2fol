// sysprove: proofs of a spec's claims, for proof_checker to check.
//   sysprove requests [--prelude L]... spec.sys claims.fol.def --req PURPOSE=OUT...
//   sysprove prove [--prelude L]... spec.sys claims.fol.def [--set PURPOSE=HEADER]... LEMMAS.def LEMMAS.proof OUT.proof
//                  --lib HEADER... [--project P --needs OUT]
//   sysprove instances --project P --lib HEADER... OUT.def OUT.proof NEEDS...
#include <fstream>
#include <iostream>
#include <set>
#include <sstream>

#include "src/prove/system.h"

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

std::pair<std::string, std::string> pair_of(const std::string& a) {
    size_t eq = a.find('=');
    if (eq == std::string::npos) throw std::runtime_error("expected PURPOSE=PATH, found " + a);
    return {a.substr(0, eq), a.substr(eq + 1)};
}

}  // namespace

int main(int argc, char** argv) {
    using namespace sys2fol;
    using namespace sys2fol::prove;
    std::vector<std::string> pos, libs, preludes;
    std::map<std::string, std::string> reqs, sets;
    std::string project, needs;
    bool partial = false;
    for (int i = 1; i < argc; ++i) {
        std::string a = argv[i];
        if (a == "--partial") partial = true;
        else if (a == "--lib" && i + 1 < argc) libs.push_back(argv[++i]);
        else if (a == "--prelude" && i + 1 < argc) preludes.push_back(argv[++i]);
        else if (a == "--req" && i + 1 < argc) reqs.insert(pair_of(argv[++i]));
        else if (a == "--set" && i + 1 < argc) sets.insert(pair_of(argv[++i]));
        else if (a == "--project" && i + 1 < argc) project = argv[++i];
        else if (a == "--needs" && i + 1 < argc) needs = argv[++i];
        else pos.push_back(a);
    }
    try {
        std::map<std::string, FmP> known;
        for (const std::string& l : libs)
            for (auto& [name, f] : read_statements(read(l), false)) known[name] = f;
        std::map<std::string, std::string> set_names;
        for (const auto& [purpose, path] : sets) {
            Claims cs = read_statements(read(path), true);
            if (cs.size() != 1) throw std::runtime_error(path + " holds " + std::to_string(cs.size()) + " claims, not one");
            set_names[purpose] = cs[0].first;
            known[cs[0].first] = cs[0].second;
        }
        if (!pos.empty() && pos[0] == "instances" && !project.empty() && pos.size() >= 3) {
            std::set<Instance> all;
            for (size_t i = 3; i < pos.size(); ++i) {
                std::istringstream lines(read(pos[i]));
                for (std::string line; std::getline(lines, line);)
                    if (!line.empty()) all.insert(from_line(line));
            }
            Lemmas lm("", known, project, true);
            for (const Instance& in : all) lm.prove_instance(in);
            std::ofstream(pos[1]) << lm.header();
            std::ofstream(pos[2]) << lm.proofs();
            return 0;
        }
        if (pos.size() < 3 || (pos[0] != "requests" && pos[0] != "prove") || (pos[0] == "prove" && pos.size() != 6) ||
            project.empty() != needs.empty()) {
            std::cerr << "usage: sysprove requests|prove ... (see the header of sysprove.cc)\n";
            return 2;
        }
        Program program;
        std::vector<Decl> forms;
        for (const std::string& p : preludes) program.load(parse(p, read(p), forms));
        program.load(parse(pos[1], read(pos[1]), forms));
        Claims claims = read_statements(read(pos[2]), true);
        std::string ns = stem(pos[1]);
        if (pos[0] == "requests") {
            std::map<std::string, std::string> rs = requests(program, claims, ns);
            for (const auto& [purpose, path] : reqs) {
                auto it = rs.find(purpose);
                if (it == rs.end()) throw std::runtime_error("no set is separated for " + purpose);
                std::ofstream(path) << it->second;
            }
            return 0;
        }
        Lemmas lm(ns, known, project);
        std::string proofs;
        int status = 0;
        try {
            proofs = prove_claims(program, claims, known, lm, set_names, ns);
        } catch (const Unproved& u) {
            std::cerr << "sysprove: " << u.what() << "\n";
            proofs = u.proofs;
            status = partial ? 0 : 1;
        }
        std::ofstream(pos[3]) << lm.header();
        std::ofstream(pos[4]) << lm.proofs();
        std::ofstream(pos[5]) << proofs;
        if (!needs.empty()) {
            std::ofstream out(needs);
            for (const Instance& in : lm.needs()) out << to_line(in) << "\n";
        }
        return status;
    } catch (const Error& e) {
        std::cerr << "sysprove: " << e.pos.line << ":" << e.pos.col << ": " << e.what() << "\n";
        return 1;
    } catch (const std::exception& e) {
        std::cerr << "sysprove: " << e.what() << "\n";
        return 1;
    }
}
