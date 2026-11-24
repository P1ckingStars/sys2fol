#include "src/lang/syntax.h"

#include <cctype>
#include <set>

namespace sys2fol {

namespace {

struct Spelling {
    const char* text;
    const char* canonical;
};

// Longest first. Unicode symbols and their ASCII spellings lex to one canonical text.
const Spelling kSymbols[] = {
    {"\xe2\x86\x92", "->"}, {"\xe2\x89\xa0", "!="}, {"\xe2\x89\xa4", "<="}, {"\xe2\x89\xa5", ">="},
    {"\xe2\x8a\x86", "subset"}, {"\xc2\xb7", "*"}, {"..<", "..<"}, {"->", "->"}, {"!=", "!="},
    {"<=", "<="}, {">=", ">="}, {"++", "++"}, {"(", "("}, {")", ")"}, {"{", "{"}, {"}", "}"},
    {"[", "["}, {"]", "]"}, {",", ","}, {":", ":"}, {"=", "="}, {".", "."}, {"|", "|"},
    {"+", "+"}, {"<", "<"}, {">", ">"}, {"*", "*"},
};

}  // namespace

std::vector<Token> lex(const std::string& s) {
    std::vector<Token> out;
    int line = 1, col = 1;
    size_t i = 0;
    auto advance = [&](size_t n) {
        for (size_t k = 0; k < n; ++k) {
            if (s[i] == '\n') {
                ++line;
                col = 1;
            } else if ((static_cast<unsigned char>(s[i]) & 0xC0) != 0x80) {
                ++col;
            }
            ++i;
        }
    };
    while (i < s.size()) {
        char c = s[i];
        if (c == ' ' || c == '\t' || c == '\r' || c == '\n') {
            advance(1);
            continue;
        }
        if (c == '-' && i + 1 < s.size() && s[i + 1] == '-') {
            while (i < s.size() && s[i] != '\n') advance(1);
            continue;
        }
        Token t;
        t.pos = {line, col};
        if (std::isalpha(static_cast<unsigned char>(c)) || c == '_') {
            size_t j = i;
            while (j < s.size() && (std::isalnum(static_cast<unsigned char>(s[j])) || s[j] == '_' || s[j] == '\'')) ++j;
            t.kind = Tok::Ident;
            t.text = s.substr(i, j - i);
            advance(j - i);
        } else if (std::isdigit(static_cast<unsigned char>(c))) {
            size_t j = i;
            while (j < s.size() && std::isdigit(static_cast<unsigned char>(s[j]))) ++j;
            t.kind = Tok::Number;
            t.text = s.substr(i, j - i);
            advance(j - i);
        } else if (c == '"') {
            size_t j = s.find('"', i + 1);
            if (j == std::string::npos) throw Error(t.pos, "a string is not closed");
            t.kind = Tok::String;
            t.text = s.substr(i + 1, j - i - 1);
            advance(j + 1 - i);
        } else {
            bool found = false;
            for (const Spelling& sp : kSymbols) {
                std::string text = sp.text;
                if (s.compare(i, text.size(), text) == 0) {
                    t.kind = Tok::Symbol;
                    t.text = sp.canonical;
                    advance(text.size());
                    found = true;
                    break;
                }
            }
            if (!found) throw Error(t.pos, std::string("unexpected character '") + c + "'");
        }
        out.push_back(t);
    }
    Token end;
    end.pos = {line + 1, 1};
    out.push_back(end);
    return out;
}

namespace {

ExprP make(Expr::Kind k, Pos p, std::string text, std::vector<ExprP> args = {}, std::string var = {}) {
    return std::make_shared<const Expr>(Expr{k, p, std::move(text), std::move(args), std::move(var)});
}

class Parser {
public:
    Parser(std::vector<Token> tokens, std::vector<Decl>& forms) : t_(std::move(tokens)), forms_(forms) {}

    std::vector<Decl> file() {
        std::vector<Decl> out;
        while (t_[i_].kind != Tok::End) {
            stop_ = 0;
            out.push_back(decl());
            if (out.back().kind == Decl::FormAlias) forms_.push_back(out.back());
        }
        return out;
    }

private:
    std::vector<Token> t_;
    size_t i_ = 0;
    int stop_ = 0;
    std::vector<Decl>& forms_;

    const Token& cur() const { return t_[i_]; }
    bool first_on_line(size_t k) const { return k == 0 || t_[k - 1].pos.line != t_[k].pos.line; }
    bool boundary() const {
        return cur().kind == Tok::End || (first_on_line(i_) && cur().pos.col <= stop_);
    }
    bool is(const char* text) const {
        return !boundary() && (cur().kind == Tok::Symbol || cur().kind == Tok::Ident) && cur().text == text;
    }
    bool accept(const char* text) {
        if (!is(text)) return false;
        ++i_;
        return true;
    }
    void expect(const char* text) {
        if (!accept(text)) throw Error(cur().pos, std::string("expected '") + text + "', found '" + cur().text + "'");
    }
    // The first token of a line or declaration, taken before its column becomes the boundary.
    std::string take_ident() {
        if (cur().kind != Tok::Ident) throw Error(cur().pos, "expected a name, found '" + cur().text + "'");
        return t_[i_++].text;
    }
    std::string ident() {
        if (boundary() || cur().kind != Tok::Ident) throw Error(cur().pos, "expected a name, found '" + cur().text + "'");
        return t_[i_++].text;
    }
    // Lines of a block: each starts on a new line, indented past `col`.
    bool block_line(int col) const {
        return cur().kind != Tok::End && first_on_line(i_) && cur().pos.col > col;
    }

    Decl decl() {
        Decl d;
        d.pos = cur().pos;
        int col = cur().pos.col;
        if (cur().kind != Tok::Ident) throw Error(cur().pos, "expected a declaration, found '" + cur().text + "'");
        std::string kw = t_[i_++].text;
        stop_ = col;
        if (kw == "use") {
            d.kind = Decl::Use;
            d.name = ident();
        } else if (kw == "extern" && is("type")) {
            ++i_;
            d.kind = Decl::ExternType;
            d.name = ident();
            expect("=");
            if (cur().kind != Tok::String) throw Error(cur().pos, "expected the fol-zfc predicate as a string");
            d.fol_name = t_[i_++].text;
        } else if (kw == "extern") {
            d.kind = Decl::Extern;
            d.name = ident();
            d.params = params();
            expect("=");
            if (cur().kind != Tok::String) throw Error(cur().pos, "expected the fol-zfc predicate as a string");
            d.fol_name = t_[i_++].text;
        } else if (kw == "type") {
            d.name = ident();
            if (is("(")) d.params = params();
            expect("=");
            if (!enum_cases(d)) {
                d.kind = Decl::TypeAlias;
                d.body = type_expr();
            }
        } else if (kw == "define") {
            d.kind = Decl::Define;
            d.name = ident();
            if (is("(")) d.params = params();
            expect("=");
            d.body = expr();
        } else if (kw == "structure") {
            structure(d, col);
        } else if (kw == "alias") {
            form_alias(d, col);
        } else if (kw == "theorem") {
            d.kind = Decl::Theorem;
            d.name = ident();
            if (is("(")) d.params = params();
            expect(":");
            stop_ = col;
            d.body = expr();
            while (block_line(col)) skip_line();
        } else if (const Decl* form = find_form(kw)) {
            instance(d, *form, col);
        } else {
            throw Error(d.pos, "'" + kw + "' does not begin a declaration");
        }
        if (!boundary()) throw Error(cur().pos, "unexpected '" + cur().text + "'");
        return d;
    }

    void skip_line() {
        int line = cur().pos.line;
        while (cur().kind != Tok::End && cur().pos.line == line) ++i_;
    }

    const Decl* find_form(const std::string& kw) const {
        for (const Decl& f : forms_)
            if (f.name == kw) return &f;
        return nullptr;
    }

    // `a | b | c`: an enum of fresh names, when every operand is a bare name.
    bool enum_cases(Decl& d) {
        size_t k = i_;
        std::vector<std::string> cases;
        while (true) {
            if (t_[k].kind != Tok::Ident) return false;
            cases.push_back(t_[k].text);
            ++k;
            bool end = t_[k].kind == Tok::End || (first_on_line(k) && t_[k].pos.col <= stop_);
            if (end) break;
            if (!(t_[k].kind == Tok::Symbol && t_[k].text == "|")) return false;
            ++k;
        }
        if (cases.size() < 2) return false;
        d.kind = Decl::Enum;
        d.cases = std::move(cases);
        i_ = k;
        return true;
    }

    std::vector<Param> params() {
        std::vector<Param> out;
        expect("(");
        size_t untyped = 0;
        while (!is(")")) {
            Param p;
            p.pos = cur().pos;
            p.name = ident();
            out.push_back(p);
            if (accept(":")) {
                ExprP type = expr();
                for (size_t k = untyped; k < out.size(); ++k) out[k].type = type;
                untyped = out.size();
            }
            if (!accept(",")) break;
        }
        expect(")");
        return out;
    }

    void structure(Decl& d, int col) {
        d.kind = Decl::Structure;
        d.name = ident();
        d.params = params();
        while (block_line(col) && !(cur().kind == Tok::Ident && cur().text == "where")) {
            int item = cur().pos.col;
            Param f;
            f.pos = cur().pos;
            f.name = take_ident();
            stop_ = item;
            expect(":");
            f.type = expr();
            d.fields.push_back(f);
            stop_ = col;
        }
        if (block_line(col) && cur().text == "where") {
            int where_col = cur().pos.col;
            ++i_;
            while (block_line(where_col)) {
                int item = cur().pos.col;
                std::string name = take_ident();
                stop_ = item;
                expect(":");
                d.conditions.push_back({name, expr()});
                stop_ = col;
            }
        }
        stop_ = col;
    }

    void form_alias(Decl& d, int col) {
        d.kind = Decl::FormAlias;
        d.name = ident();
        expect("=");
        expect("instance");
        expect("of");
        d.structure = ident();
        while (block_line(col)) {
            int item = cur().pos.col;
            bool first = true;
            do {
                std::string keyword = first ? take_ident() : ident();
                first = false;
                stop_ = item;
                expect("for");
                d.renames.push_back({keyword, ident()});
            } while (accept(","));
            stop_ = col;
        }
    }

    void instance(Decl& d, const Decl& form, int col) {
        d.kind = Decl::Instance;
        d.structure = form.structure;
        d.form = form.name;
        d.name = ident();
        if (is("(")) d.params = params();
        auto field_for = [&](const std::string& keyword) -> std::string {
            for (const auto& [k, field] : form.renames)
                if (k == keyword) return field;
            return {};
        };
        while (block_line(col)) {
            int item = cur().pos.col;
            Pos pos = cur().pos;
            if (cur().kind == Tok::Ident && cur().text == "on") {
                stop_ = item;
                std::string field = field_for("rules");
                if (field.empty()) throw Error(pos, "this form has no field written as rules");
                FieldContent& c = d.contents[field];
                if (c.rules.empty()) c.pos = pos;
                c.kind = FieldContent::Rules;
                c.rules.push_back(rule());
            } else {
                std::string keyword = take_ident();
                stop_ = item;
                std::string field = field_for(keyword);
                if (field.empty()) throw Error(pos, "'" + keyword + "' names no field of " + form.structure);
                FieldContent& c = d.contents[field];
                c.pos = pos;
                if (cur().kind == Tok::Ident && t_[i_ + 1].kind == Tok::Symbol && t_[i_ + 1].text == ":") {
                    c.kind = FieldContent::Parts;
                    do {
                        Part p;
                        p.pos = cur().pos;
                        p.name = ident();
                        expect(":");
                        p.type = type_expr();
                        c.parts.push_back(p);
                    } while (accept(","));
                } else {
                    c.kind = FieldContent::Condition;
                    c.condition = expr();
                }
            }
            stop_ = col;
        }
    }

    Rule rule() {
        Rule r;
        r.pos = cur().pos;
        ++i_;
        if (!accept("any")) {
            ExprP e = postfix();
            if (accept("=")) {
                if (e->kind != Expr::Name) throw Error(e->pos, "a rule tests a port by its name");
                r.port = e->text;
                r.value = expr();
            } else {
                r.value = e;
            }
        }
        if (accept("when")) r.guard = expr();
        expect("->");
        if (!accept("unchanged")) r.description = expr();
        return r;
    }

    // A type: an enum whose cases may carry fields (`took(job: Job) | empty`), or an expression.
    ExprP type_expr() {
        size_t start = i_;
        Pos p = cur().pos;
        std::vector<ExprP> cases;
        while (cur().kind == Tok::Ident && !boundary()) {
            Pos cp = cur().pos;
            std::string name = t_[i_++].text;
            std::vector<ExprP> types;
            std::vector<std::string> names;
            if (is("(") && !first_on_line(i_))
                for (const Param& f : params()) {
                    if (!f.type) throw Error(f.pos, "a case's field needs its type");
                    names.push_back(f.name);
                    types.push_back(f.type);
                }
            auto c = std::make_shared<Expr>(Expr{Expr::Case, cp, name, std::move(types), {}});
            c->names = std::move(names);
            cases.push_back(c);
            if (!accept("|")) break;
        }
        if (cases.size() >= 2 && (boundary() || !(cur().kind == Tok::Symbol && cur().text != "," && cur().text != ")")))
            return make(Expr::Enum, p, "", std::move(cases));
        i_ = start;
        return expr();
    }

    // Expressions, loosest first.
    ExprP expr() { return implies(); }

    ExprP implies() {
        ExprP l = disj();
        if (is("implies")) {
            Pos p = cur().pos;
            ++i_;
            return make(Expr::Binary, p, "implies", {l, implies()});
        }
        return l;
    }
    ExprP disj() {
        ExprP l = conj();
        while (is("or")) {
            Pos p = cur().pos;
            ++i_;
            l = make(Expr::Binary, p, "or", {l, conj()});
        }
        return l;
    }
    ExprP conj() {
        ExprP l = negation();
        while (is("and")) {
            Pos p = cur().pos;
            ++i_;
            l = make(Expr::Binary, p, "and", {l, negation()});
        }
        return l;
    }
    ExprP negation() {
        if (is("not")) {
            Pos p = cur().pos;
            ++i_;
            return make(Expr::Unary, p, "not", {negation()});
        }
        return comparison();
    }
    ExprP comparison() {
        ExprP l = sum();
        static const std::set<std::string> ops = {"=", "!=", "<", "<=", ">", ">=", "subset", "in"};
        if (!boundary() && ops.count(cur().text) && (cur().kind == Tok::Symbol || cur().text == "in" || cur().text == "subset")) {
            Pos p = cur().pos;
            std::string op = t_[i_++].text;
            return make(Expr::Binary, p, op, {l, sum()});
        }
        return l;
    }
    ExprP sum() {
        ExprP l = postfix();
        while (is("+") || is("++") || is("..<")) {
            Pos p = cur().pos;
            std::string op = t_[i_++].text;
            ExprP r = postfix();
            l = op == "..<" ? make(Expr::Range, p, op, {l, r}) : make(Expr::Binary, p, op, {l, r});
        }
        return l;
    }
    ExprP postfix() {
        ExprP e = primary();
        while (true) {
            if (is(".")) {
                Pos p = cur().pos;
                ++i_;
                e = make(Expr::Field, p, ident(), {e});
            } else if (is("(") && !first_on_line(i_)) {
                Pos p = cur().pos;
                ++i_;
                std::vector<ExprP> args{e};
                if (!is(")")) {
                    do args.push_back(expr());
                    while (accept(","));
                }
                expect(")");
                e = make(Expr::Call, p, "", std::move(args));
            } else {
                return e;
            }
        }
    }
    ExprP primary() {
        if (boundary()) throw Error(cur().pos, "an expression is missing");
        Pos p = cur().pos;
        if (cur().kind == Tok::Number) return make(Expr::Number, p, t_[i_++].text);
        if (accept("(")) {
            std::vector<ExprP> items{expr()};
            while (accept(",")) items.push_back(expr());
            expect(")");
            return make(Expr::Paren, p, "", std::move(items));
        }
        if ((is("set") || is("sequence")) && t_[i_ + 1].kind == Tok::Ident && t_[i_ + 1].text == "of") {
            std::string op = t_[i_].text + " of";
            i_ += 2;
            return make(Expr::Unary, p, op, {postfix()});
        }
        if (accept("[")) {
            std::vector<ExprP> items;
            if (!is("]")) {
                do items.push_back(expr());
                while (accept(","));
            }
            expect("]");
            return make(Expr::SeqLit, p, "", std::move(items));
        }
        if (accept("{")) {
            std::string v = ident();
            expect("in");
            ExprP bound = expr();
            expect("|");
            ExprP cond = expr();
            expect("}");
            return make(Expr::SetOf, p, "", {bound, cond}, v);
        }
        if (is("all") || is("some")) {
            std::string q = t_[i_++].text;
            std::string v = ident();
            expect("in");
            ExprP bound = expr();
            expect(":");
            return make(Expr::Quant, p, q, {bound, expr()}, v);
        }
        if (accept("next")) return make(Expr::Next, p, ident());
        return make(Expr::Name, p, ident());
    }
};

std::string op_text(const std::string& op) {
    if (op == "!=") return "\xe2\x89\xa0";
    if (op == "<=") return "\xe2\x89\xa4";
    if (op == ">=") return "\xe2\x89\xa5";
    if (op == "subset") return "\xe2\x8a\x86";
    return op;
}

}  // namespace

Source parse(const std::string& path, const std::string& text, std::vector<Decl>& forms) {
    Parser p(lex(text), forms);
    return Source{path, p.file()};
}

std::string show(const Expr& e) {
    switch (e.kind) {
        case Expr::Name:
        case Expr::Number: return e.text;
        case Expr::Paren: {
            std::string s = "(";
            for (size_t k = 0; k < e.args.size(); ++k) s += (k ? ", " : "") + show(*e.args[k]);
            return s + ")";
        }
        case Expr::Next: return "next " + e.text;
        case Expr::Field: return show(*e.args[0]) + "." + e.text;
        case Expr::Unary: return e.text + " " + show(*e.args[0]);
        case Expr::Binary: return show(*e.args[0]) + " " + op_text(e.text) + " " + show(*e.args[1]);
        case Expr::Range: return show(*e.args[0]) + " ..< " + show(*e.args[1]);
        case Expr::SetOf: return "{ " + e.var + " in " + show(*e.args[0]) + " | " + show(*e.args[1]) + " }";
        case Expr::Quant: return e.text + " " + e.var + " in " + show(*e.args[0]) + ": " + show(*e.args[1]);
        case Expr::Call: {
            std::string s = show(*e.args[0]) + "(";
            for (size_t k = 1; k < e.args.size(); ++k) s += (k > 1 ? ", " : "") + show(*e.args[k]);
            return s + ")";
        }
        case Expr::SeqLit: {
            std::string s = "[";
            for (size_t k = 0; k < e.args.size(); ++k) s += (k ? ", " : "") + show(*e.args[k]);
            return s + "]";
        }
        case Expr::Enum: {
            std::string s;
            for (size_t k = 0; k < e.args.size(); ++k) s += (k ? " | " : "") + show(*e.args[k]);
            return s;
        }
        case Expr::Case: {
            std::string s = e.text;
            for (size_t k = 0; k < e.args.size(); ++k) s += (k ? ", " : "(") + e.names[k] + ": " + show(*e.args[k]);
            return e.args.empty() ? s : s + ")";
        }
    }
    return {};
}

}  // namespace sys2fol
