#pragma once

#include <map>
#include <memory>
#include <stdexcept>
#include <string>
#include <vector>

namespace sys2fol {

struct Pos {
    int line = 0;
    int col = 0;
};

struct Error : std::runtime_error {
    Pos pos;
    Error(Pos p, const std::string& message) : std::runtime_error(message), pos(p) {}
};

enum class Tok { Ident, Number, String, Symbol, End };

struct Token {
    Tok kind = Tok::End;
    std::string text;
    Pos pos;
};

std::vector<Token> lex(const std::string& source);

// Surface syntax, as written. Names are resolved later (core.h).
struct Expr;
using ExprP = std::shared_ptr<const Expr>;

struct Expr {
    enum Kind { Name, Number, Call, Field, Next, Unary, Binary, SetOf, Quant, Range, Paren, SeqLit, Enum, Case };
    Kind kind;
    Pos pos;
    std::string text;            // a name, a number, a field, an operator, a quantifier; Case: its name
    std::vector<ExprP> args;     // operands; SetOf, Quant: bound set, then body; Enum: its cases; Case: field types
    std::string var;             // the bound variable of SetOf and Quant
    std::vector<std::string> names;  // Case: its fields
};

struct Param {
    std::string name;
    ExprP type;                  // null: an unconstrained term
    Pos pos;
};

struct Part {                    // `name : type` in a field written as a list of parts
    std::string name;
    ExprP type;
    Pos pos;
};

struct Rule {
    Pos pos;
    std::string port;            // `on port = value`; empty for `on any`
    ExprP value;
    ExprP guard;                 // null when there is no `when`
    ExprP description;           // null when `unchanged`
};

struct FieldContent {
    enum Kind { Parts, Condition, Rules };
    Kind kind = Parts;
    Pos pos;
    std::vector<Part> parts;
    ExprP condition;
    std::vector<Rule> rules;
};

struct Decl {
    enum Kind { Use, Extern, ExternType, TypeAlias, Enum, Define, Structure, FormAlias, Instance, Theorem };
    Kind kind;
    Pos pos;
    std::string name;
    std::vector<Param> params;
    ExprP body;                                          // TypeAlias, Define; Theorem: the claim
    std::string fol_name;                                // Extern, ExternType
    std::vector<std::string> cases;                      // Enum
    std::vector<Param> fields;                           // Structure
    std::vector<std::pair<std::string, ExprP>> conditions;
    std::string structure;                               // FormAlias, Instance
    std::string form;                                    // Instance: the form alias it is written in
    std::vector<std::pair<std::string, std::string>> renames;  // FormAlias: keyword, field
    std::map<std::string, FieldContent> contents;        // Instance: field, content
};

struct Source {
    std::string path;
    std::vector<Decl> decls;
};

// `forms` holds the form aliases declared so far, by keyword; parsing adds the file's own.
Source parse(const std::string& path, const std::string& text, std::vector<Decl>& forms);

std::string show(const Expr& e);

}  // namespace sys2fol
