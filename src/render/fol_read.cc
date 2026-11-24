#include "src/render/fol_read.h"

#include <stdexcept>

#include "src/parser/parser.h"

namespace sys2fol::render {

namespace {

FP convert(const logic::Formula& f, int depth) {
    auto n = std::make_shared<F>();
    if (f.is_predicate()) {
        const logic::PredicateInstance& p = f.as_predicate();
        n->kind = F::Atom;
        n->pred = p.predicate().get().get_name();
        for (const logic::Term& t : p.args()) {
            if (!t.is_generalized()) throw std::runtime_error("a claim's terms are its bound variables");
            n->args.push_back(depth - 1 - static_cast<int>(t.as_variable()));
        }
        return n;
    }
    if (f.is_compound()) {
        const logic::Compound& c = f.as_compound();
        switch (c.op) {
            case logic::Op::Bottom: n->kind = F::False; return n;
            case logic::Op::Not: n->kind = F::Not; break;
            case logic::Op::And: n->kind = F::And; break;
            case logic::Op::Or: n->kind = F::Or; break;
            case logic::Op::Implies: n->kind = F::Implies; break;
            case logic::Op::Iff: n->kind = F::Iff; break;
            default: throw std::runtime_error("an unknown connective");
        }
        n->kids.push_back(convert(c.left.get(), depth));
        if (c.op != logic::Op::Not) n->kids.push_back(convert(c.right.get(), depth));
        return n;
    }
    if (f.is_quantified()) {
        const logic::Quantified& q = f.as_quantified();
        n->kind = q.op == logic::Op::Forall ? F::All : F::Ex;
        n->var = depth;
        n->kids.push_back(convert(q.body.get(), depth + 1));
        return n;
    }
    throw std::runtime_error("a claim the renderer cannot read: it refers to a sentence or a schema variable");
}

}  // namespace

std::vector<FolClaim> read_claims(const std::string& text) {
    logic::GlobalContext ctx;
    std::vector<FolClaim> out;
    for (const logic::ParsedStatement& s : logic::parse_statements(text, ctx))
        if (s.kind == logic::ParsedStatement::Kind::Claim)
            out.push_back({s.name, convert(s.formula.get().root().get(), 0)});
    return out;
}

std::string show(const FP& f) {
    auto v = [](int d) { return "v" + std::to_string(d); };
    switch (f->kind) {
        case F::Atom: {
            std::string s = f->pred + "(";
            for (size_t i = 0; i < f->args.size(); ++i) s += (i ? ", " : "") + v(f->args[i]);
            return s + ")";
        }
        case F::False: return "false";
        case F::Not: return "(~ " + show(f->kids[0]) + ")";
        case F::All: return "(forall " + v(f->var) + ". " + show(f->kids[0]) + ")";
        case F::Ex: return "(exists " + v(f->var) + ". " + show(f->kids[0]) + ")";
        default: {
            const char* op = f->kind == F::And ? " & " : f->kind == F::Or ? " | " : f->kind == F::Implies ? " -> " : " <-> ";
            return "(" + show(f->kids[0]) + op + show(f->kids[1]) + ")";
        }
    }
}

}  // namespace sys2fol::render
