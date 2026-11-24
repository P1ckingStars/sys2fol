#include "src/prove/lemmas.h"

#include <stdexcept>

namespace sys2fol::prove {

namespace {

std::vector<std::string> names(const std::string& hint, size_t n) {
    std::vector<std::string> xs;
    for (size_t i = 0; i < n; ++i) xs.push_back(fresh(hint));
    return xs;
}

// (forall x0. (set(x0) -> ... body)) over the given names.
FmP all_of(const std::vector<std::string>& xs, FmP body) {
    for (size_t i = xs.size(); i-- > 0;) body = all(xs[i], body);
    return body;
}

// Proves all_of(xs, ...) with fresh variables, body(xs).
H intro_all(Tac& t, size_t n, const std::string& hint,
            const std::function<H(const std::vector<std::string>&)>& body) {
    std::vector<std::string> xs;
    std::function<H(size_t)> go = [&](size_t i) -> H {
        if (i == n) return body(xs);
        return t.all(hint, [&](const std::string& x) {
            xs.push_back(x);
            H h = go(i + 1);
            xs.pop_back();
            return h;
        });
    };
    return go(0);
}

H zero_unfold(Tac& t, const std::string& z, H g) {
    return t.p.iff_l(t.p.forall_elim(t.p.use("zero_def"), z), g);
}

}  // namespace

H refl(Tac& t, const std::string& x) { return t.p.forall_elim(t.p.use("eq_refl"), x); }

H intro_chain(Tac& t, size_t k, const std::function<H(const std::vector<std::string>&, const std::vector<H>&)>& body) {
    std::vector<std::string> zs;
    std::vector<H> gs;
    std::function<H(size_t)> go = [&](size_t i) -> H {
        if (i == k + 1) return body(zs, gs);
        return t.all("z", [&](const std::string& z) {
            FmP guard = i == 0 ? atom("zero", {z}) : atom("nsucc", {zs.back(), z});
            zs.push_back(z);
            H h = t.assume(guard, [&](H g) {
                gs.push_back(g);
                H r = go(i + 1);
                gs.pop_back();
                return r;
            });
            zs.pop_back();
            return h;
        });
    };
    return go(0);
}

H use_chain(Tac& t, H h, const std::vector<std::string>& zs, const std::vector<H>& guards) {
    for (size_t i = 0; i < zs.size(); ++i) h = t.mp(t.inst(h, {zs[i]}), {guards[i]});
    return h;
}

H canonical(Tac& t, size_t k, const std::function<H(const std::vector<std::string>&, const std::vector<H>&)>& body) {
    std::vector<std::string> zs;
    std::vector<H> gs;
    std::function<H(size_t)> go = [&](size_t i) -> H {
        if (i == k + 1) return body(zs, gs);
        H ex = i == 0 ? t.p.use("zero_EX") : t.inst(t.p.use("nsucc_EX"), {zs.back()});
        return t.obtain(ex, "c", [&](const std::string& z, H g) {
            zs.push_back(z);
            gs.push_back(g);
            H h = go(i + 1);
            zs.pop_back();
            gs.pop_back();
            return h;
        });
    };
    return go(0);
}

std::vector<H> chains_equal(Tac& t, const std::vector<std::string>& a, const std::vector<H>& ga,
                            const std::vector<std::string>& b, const std::vector<H>& gb) {
    std::vector<H> eqs;
    for (size_t i = 0; i < a.size() && i < b.size(); ++i) {
        if (i == 0) {
            eqs.push_back(t.mp(t.inst(t.p.use("zero_UNIQ"), {a[0], b[0]}), {ga[0], gb[0]}));
        } else {
            H e = t.inst(t.p.use("nsucc_eq"), {a[i - 1], b[i - 1], a[i], b[i]});
            eqs.push_back(t.mp(e, {eqs.back(), ga[i], gb[i]}));
        }
    }
    return eqs;
}

H succ_unfold(Tac& t, const std::string& n, const std::string& m, H g) {
    return t.p.iff_l(t.inst(t.p.use("nsucc_def"), {n, m}), g);
}

H inject(Tac& t, H h, const std::vector<FmP>& ds, size_t j) {
    if (j + 1 < ds.size()) h = t.p.or_intro_l(h, disj(std::vector<FmP>(ds.begin() + j + 1, ds.end())));
    for (size_t i = j; i-- > 0;) h = t.p.or_intro_r(ds[i], h);
    return h;
}

std::string Lemmas::make(const std::string& base, const std::function<FmP()>& statement,
                         const std::function<H(Tac&)>& proof) {
    std::string name = ns_ + ".lemma." + base;
    if (made_.count(name)) return name;
    made_[name] = true;
    FmP s = statement();
    Proof p(name, known_);
    Tac t(p);
    H h = proof(t);
    if (!alpha_eq(p.fm(h), s))
        throw std::runtime_error("the proof of " + name + " ends with " + print(p.fm(h)).substr(0, 400) + ", not " +
                                 print(s).substr(0, 400));
    p.qed(h);
    proofs_ += p.text() + "\n";
    claims_.push_back({name, s});
    known_[name] = s;
    return name;
}

std::string Lemmas::header() const {
    std::string s = "# Written by sysprove: facts about numbers and records the spec's proofs cite.\n";
    for (const auto& [name, f] : claims_) s += "\nclaim " + name + ": " + print(f) + "\n";
    return s;
}

std::string Lemmas::canon(uint64_t c) {
    return make("canon_" + std::to_string(c),
                [&] { return enc::chain(c, [&](const std::vector<std::string>& z) { return enc::num(c, z[c]); }); },
                [&](Tac& t) {
                    return intro_chain(t, c, [&](const std::vector<std::string>& z, const std::vector<H>& g) -> H {
                        if (c == 0) return g[0];
                        return intro_chain(t, c - 1, [&](const std::vector<std::string>& w, const std::vector<H>& gw) {
                            std::vector<H> e = chains_equal(t, w, gw, z, g);
                            H cong = t.inst(t.p.use("nsucc_CONG"), {z[c - 1], w[c - 1], z[c]});
                            return t.mp(cong, {t.p.eq_sym(e[c - 1]), g[c]});
                        });
                    });
                });
}

std::string Lemmas::is_canon(uint64_t c) {
    auto statement = [&] {
        std::string x = fresh("_x");
        return all(x, imp(enc::num(c, x), enc::chain(c, [&](const std::vector<std::string>& z) {
                              return atom("eq", {x, z[c]});
                          })));
    };
    return make("is_canon_" + std::to_string(c), statement, [&](Tac& t) {
        return t.all("x", [&](const std::string& x) {
            return t.assume(enc::num(c, x), [&](H num) {
                return intro_chain(t, c, [&](const std::vector<std::string>& z, const std::vector<H>& g) {
                    if (c == 0) return t.mp(t.inst(t.p.use("zero_UNIQ"), {x, z[0]}), {num, g[0]});
                    H n = use_chain(t, num, std::vector<std::string>(z.begin(), z.begin() + c),
                                    std::vector<H>(g.begin(), g.begin() + c));
                    return t.mp(t.inst(t.p.use("nsucc_UNIQ"), {z[c - 1], x, z[c]}), {n, g[c]});
                });
            });
        });
    });
}

std::string Lemmas::below(uint64_t c, uint64_t d) {
    auto statement = [&] {
        return enc::chain(d, [&](const std::vector<std::string>& z) { return atom("elem", {z[c], z[d]}); });
    };
    return make("below_" + std::to_string(c) + "_" + std::to_string(d), statement, [&](Tac& t) {
        return intro_chain(t, d, [&](const std::vector<std::string>& z, const std::vector<H>& g) {
            H u = t.inst(succ_unfold(t, z[c], z[c + 1], g[c + 1]), {z[c]});
            H e = t.p.iff_r(u, t.p.or_intro_r(atom("elem", {z[c], z[c]}), refl(t, z[c])));
            for (uint64_t k = c + 1; k < d; ++k) {
                H uk = t.inst(succ_unfold(t, z[k], z[k + 1], g[k + 1]), {z[c]});
                e = t.p.iff_r(uk, t.p.or_intro_l(e, atom("eq", {z[c], z[k]})));
            }
            return e;
        });
    });
}

std::string Lemmas::distinct(uint64_t c, uint64_t d) {
    std::string b = below(c, d);
    auto statement = [&] {
        return enc::chain(d, [&](const std::vector<std::string>& z) { return neg(atom("eq", {z[c], z[d]})); });
    };
    return make("distinct_" + std::to_string(c) + "_" + std::to_string(d), statement, [&](Tac& t) {
        return intro_chain(t, d, [&](const std::vector<std::string>& z, const std::vector<H>& g) {
            return t.refute(atom("eq", {z[c], z[d]}), [&](H h) {
                H m = use_chain(t, t.p.use(b), z, g);
                H e = t.mp(t.inst(t.p.use("elem_second"), {z[d], z[c], z[c]}), {t.p.eq_sym(h), m});
                return t.p.not_elim(t.inst(t.p.use("no_self_member"), {z[c]}), e);
            });
        });
    });
}

std::string Lemmas::num_cong(uint64_t c) {
    auto statement = [&] {
        std::string x = fresh("_x"), y = fresh("_y");
        return all(x, all(y, imp(atom("eq", {x, y}), imp(enc::num(c, x), enc::num(c, y)))));
    };
    return make("num_cong_" + std::to_string(c), statement, [&](Tac& t) {
        return intro_all(t, 2, "x", [&](const std::vector<std::string>& v) {
            const std::string &x = v[0], &y = v[1];
            return t.assume(atom("eq", {x, y}), [&](H heq) {
                return t.assume(enc::num(c, x), [&](H hx) -> H {
                    if (c == 0) {
                        H none = t.all("u", [&](const std::string& u) {
                            return t.refute(atom("elem", {u, y}), [&](H h) {
                                H e = t.mp(t.inst(t.p.use("elem_second"), {y, x, u}), {t.p.eq_sym(heq), h});
                                return t.p.not_elim(t.inst(zero_unfold(t, x, hx), {u}), e);
                            });
                        });
                        return t.p.iff_r(t.p.forall_elim(t.p.use("zero_def"), y), none);
                    }
                    return intro_chain(t, c - 1, [&](const std::vector<std::string>& w, const std::vector<H>& g) {
                        const std::string& n = w[c - 1];
                        H ux = succ_unfold(t, n, x, use_chain(t, hx, w, g));
                        H body = t.all("u", [&](const std::string& u) {
                            H a = t.inst(ux, {u});
                            H cr = t.mp(t.inst(t.p.use("cong_elem_r"), {u, x, y}), {heq});
                            FmP d = t.p.fm(a)->b;
                            H l = t.assume(atom("elem", {u, y}), [&](H h) { return t.p.iff_l(a, t.p.iff_r(cr, h)); });
                            H r = t.assume(d, [&](H h) { return t.p.iff_l(cr, t.p.iff_r(a, h)); });
                            return t.p.iff_intro(l, r);
                        });
                        return t.p.iff_r(t.inst(t.p.use("nsucc_def"), {n, y}), body);
                    });
                });
            });
        });
    });
}

std::string Lemmas::at(size_t k, size_t i) {
    auto statement = [&] {
        std::string r = fresh("_r");
        std::vector<std::string> xs = names("_x", k);
        std::vector<std::string> vars{r};
        vars.insert(vars.end(), xs.begin(), xs.end());
        return all_of(vars, imp(enc::rec(r, xs), enc::at(i, xs[i], r)));
    };
    return make("at_" + std::to_string(k) + "_" + std::to_string(i), statement, [&](Tac& t) {
        return intro_all(t, k + 1, "x", [&](const std::vector<std::string>& v) {
            const std::string& r = v[0];
            std::vector<std::string> xs(v.begin() + 1, v.end());
            return t.assume(enc::rec(r, xs), [&](H rec) {
                return intro_chain(t, i, [&](const std::vector<std::string>& z, const std::vector<H>& g) {
                    std::vector<std::string> zz = z;
                    std::vector<H> gg = g;
                    std::function<H()> extend = [&]() -> H {
                        if (zz.size() == k + 1) return t.split(use_chain(t, rec, zz, gg), k + 1)[i + 1];
                        return t.obtain(t.inst(t.p.use("nsucc_EX"), {zz.back()}), "c", [&](const std::string& m, H gm) {
                            zz.push_back(m);
                            gg.push_back(gm);
                            H h = extend();
                            zz.pop_back();
                            gg.pop_back();
                            return h;
                        });
                    };
                    return extend();
                });
            });
        });
    });
}

std::string Lemmas::at_fun(size_t k, size_t i) {
    auto statement = [&] {
        std::string r = fresh("_r"), v = fresh("_v");
        std::vector<std::string> xs = names("_x", k);
        std::vector<std::string> vars{r};
        vars.insert(vars.end(), xs.begin(), xs.end());
        vars.push_back(v);
        return all_of(vars, imp(enc::rec(r, xs), imp(enc::at(i, v, r), atom("eq", {v, xs[i]}))));
    };
    return make("at_fun_" + std::to_string(k) + "_" + std::to_string(i), statement, [&](Tac& t) {
        return intro_all(t, k + 2, "x", [&](const std::vector<std::string>& vs) {
            const std::string& r = vs[0];
            const std::string& v = vs[k + 1];
            std::vector<std::string> xs(vs.begin() + 1, vs.begin() + 1 + k);
            return t.assume(enc::rec(r, xs), [&](H rec) {
                return t.assume(enc::at(i, v, r), [&](H hat) {
                    return canonical(t, k, [&](const std::vector<std::string>& z, const std::vector<H>& g) {
                        std::vector<H> parts = t.split(use_chain(t, rec, z, g), k + 1);
                        H pv = use_chain(t, hat, std::vector<std::string>(z.begin(), z.begin() + i + 1),
                                         std::vector<H>(g.begin(), g.begin() + i + 1));
                        H td = t.p.iff_l(t.inst(t.p.use("tuple_def"), {r, z[k]}), parts[0]);
                        H fun = t.split(td, 4)[3];
                        return t.mp(t.inst(fun, {z[i], v, xs[i]}), {pv, parts[i + 1]});
                    });
                });
            });
        });
    });
}

std::string Lemmas::at_cong(size_t i) {
    auto statement = [&] {
        std::string r = fresh("_r"), r2 = fresh("_r"), v = fresh("_v");
        return all(r, all(r2, all(v, imp(atom("eq", {r, r2}), imp(enc::at(i, v, r), enc::at(i, v, r2))))));
    };
    return make("at_cong_" + std::to_string(i), statement, [&](Tac& t) {
        return intro_all(t, 3, "x", [&](const std::vector<std::string>& vs) {
            const std::string &r = vs[0], &r2 = vs[1], &v = vs[2];
            return t.assume(atom("eq", {r, r2}), [&](H heq) {
                return t.assume(enc::at(i, v, r), [&](H hat) {
                    return intro_chain(t, i, [&](const std::vector<std::string>& z, const std::vector<H>& g) {
                        H pv = use_chain(t, hat, z, g);
                        H pd = t.p.iff_l(t.inst(t.p.use("pmem_def"), {z[i], v, r}), pv);
                        return t.obtain(pd, "p", [&](const std::string& p, H body) {
                            std::vector<H> kp = t.split(body, 2);
                            H ep = t.mp(t.inst(t.p.use("elem_second"), {r, r2, p}), {heq, kp[1]});
                            H w = t.witness(t.p.and_intro(kp[0], ep), p);
                            return t.p.iff_r(t.inst(t.p.use("pmem_def"), {z[i], v, r2}), w);
                        });
                    });
                });
            });
        });
    });
}

std::string Lemmas::pmem_cong1() {
    auto statement = [&] {
        std::string i = fresh("_i"), j = fresh("_j"), y = fresh("_y"), x = fresh("_t");
        return all(i, all(j, all(y, all(x, imp(atom("eq", {i, j}), imp(atom("pmem", {i, y, x}), atom("pmem", {j, y, x})))))));
    };
    return make("pmem_cong1", statement, [&](Tac& t) {
        return intro_all(t, 4, "x", [&](const std::vector<std::string>& vs) {
            const std::string &i = vs[0], &j = vs[1], &y = vs[2], &x = vs[3];
            return t.assume(atom("eq", {i, j}), [&](H heq) {
                return t.assume(atom("pmem", {i, y, x}), [&](H hp) {
                    H pd = t.p.iff_l(t.inst(t.p.use("pmem_def"), {i, y, x}), hp);
                    return t.obtain(pd, "p", [&](const std::string& p, H body) {
                        std::vector<H> kp = t.split(body, 2);
                        H k2 = t.mp(t.inst(t.p.use("kpair_arg_cong"), {i, y, j, y, p}), {kp[0], heq, refl(t, y)});
                        H w = t.witness(t.p.and_intro(k2, kp[1]), p);
                        return t.p.iff_r(t.inst(t.p.use("pmem_def"), {j, y, x}), w);
                    });
                });
            });
        });
    });
}

std::string Lemmas::tuple_cong2() {
    auto statement = [&] {
        std::string x = fresh("_t"), n = fresh("_n"), m = fresh("_m");
        return all(x, all(n, all(m, imp(atom("eq", {n, m}), imp(atom("tuple", {x, n}), atom("tuple", {x, m}))))));
    };
    return make("tuple_cong2", statement, [&](Tac& t) {
        return intro_all(t, 3, "x", [&](const std::vector<std::string>& vs) {
            const std::string &x = vs[0], &n = vs[1], &m = vs[2];
            return t.assume(atom("eq", {n, m}), [&](H heq) {
                return t.assume(atom("tuple", {x, n}), [&](H ht) {
                    std::vector<H> td = t.split(t.p.iff_l(t.inst(t.p.use("tuple_def"), {x, n}), ht), 4);
                    H hme = t.p.eq_sym(heq);
                    std::vector<H> id = t.split(t.p.iff_l(t.p.forall_elim(t.p.use("index_def"), n), td[0]), 2);
                    H trans = t.all("u", [&](const std::string& u) {
                        return t.assume(atom("elem", {u, m}), [&](H hu) {
                            H un = t.mp(t.inst(t.p.use("elem_second"), {m, n, u}), {hme, hu});
                            H inner = t.mp(t.inst(id[0], {u}), {un});
                            return t.all("w", [&](const std::string& w) {
                                return t.assume(atom("elem", {w, u}), [&](H hw) {
                                    H wn = t.mp(t.inst(inner, {w}), {hw});
                                    return t.mp(t.inst(t.p.use("elem_second"), {n, m, w}), {heq, wn});
                                });
                            });
                        });
                    });
                    H nself = t.refute(atom("elem", {m, m}), [&](H h) {
                        H e1 = t.mp(t.inst(t.p.use("elem_first_subst"), {m, n, m}), {hme, h});
                        H e2 = t.mp(t.inst(t.p.use("elem_second"), {m, n, n}), {hme, e1});
                        return t.p.not_elim(id[1], e2);
                    });
                    H idx = t.p.iff_r(t.p.forall_elim(t.p.use("index_def"), m), t.p.and_intro(trans, nself));
                    H a = t.all("u", [&](const std::string& u) {
                        return t.assume(atom("elem", {u, x}), [&](H hu) {
                            H ex = t.mp(t.inst(td[1], {u}), {hu});
                            return t.obtain(ex, "i", [&](const std::string& i, H body) {
                                std::vector<H> b = t.split(body, 2);
                                H im = t.mp(t.inst(t.p.use("elem_second"), {n, m, i}), {heq, b[0]});
                                return t.witness(t.p.and_intro(im, b[1]), i);
                            });
                        });
                    });
                    H b = t.all("i", [&](const std::string& i) {
                        return t.assume(atom("elem", {i, m}), [&](H hi) {
                            return t.mp(t.inst(td[2], {i}), {t.mp(t.inst(t.p.use("elem_second"), {m, n, i}), {hme, hi})});
                        });
                    });
                    return t.p.iff_r(t.inst(t.p.use("tuple_def"), {x, m}), t.join({idx, a, b, td[3]}));
                });
            });
        });
    });
}

std::string Lemmas::rec_ex(size_t k) {
    std::string tc = tuple_cong2(), pc = pmem_cong1();
    auto statement = [&] {
        std::vector<std::string> xs = names("_x", k);
        std::string r = fresh("_r");
        return all_of(xs, some(r, enc::rec(r, xs)));
    };
    return make("rec_ex_" + std::to_string(k), statement, [&](Tac& t) {
        return intro_all(t, k, "x", [&](const std::vector<std::string>& xs) {
            return canonical(t, k, [&](const std::vector<std::string>& z, const std::vector<H>& g) {
                H tz = t.mp(t.p.forall_elim(t.p.use("tuple_zero"), z[0]), {zero_unfold(t, z[0], g[0])});
                std::vector<H> pm;
                std::function<H(size_t, const std::string&, H)> build = [&](size_t j, const std::string& r, H tup) -> H {
                    if (j == k) {
                        H rec = intro_chain(t, k, [&](const std::vector<std::string>& w, const std::vector<H>& gw) {
                            std::vector<H> e = chains_equal(t, z, g, w, gw);
                            std::vector<H> parts{t.mp(t.inst(t.p.use(tc), {r, z[k], w[k]}), {e[k], tup})};
                            for (size_t l = 0; l < k; ++l)
                                parts.push_back(t.mp(t.inst(t.p.use(pc), {z[l], w[l], xs[l], r}), {e[l], pm[l]}));
                            return t.join(parts);
                        });
                        return t.witness(rec, r);
                    }
                    H sx = t.inst(t.p.use("snoc_EX"), {r, z[j], xs[j]});
                    return t.obtain(sx, "s", [&](const std::string& s, H snoc) {
                        H f = t.mp(t.inst(t.p.use("snoc_facts"), {z[j], z[j + 1]}), {g[j + 1]});
                        f = t.mp(t.inst(f, {r, xs[j], s}), {tup, snoc});
                        std::vector<H> facts = t.split(f, 3);
                        std::vector<H> saved = pm;
                        for (size_t l = 0; l < pm.size(); ++l) pm[l] = t.mp(t.inst(facts[2], {z[l], xs[l]}), {pm[l]});
                        pm.push_back(facts[1]);
                        H h = build(j + 1, s, facts[0]);
                        pm = saved;
                        return h;
                    });
                };
                return build(0, z[0], tz);
            });
        });
    });
}

std::string Lemmas::index_cases(size_t k) {
    auto statement = [&] {
        return enc::chain(k, [&](const std::vector<std::string>& z) {
            std::string i = fresh("_i");
            std::vector<FmP> ds;
            for (size_t j = 0; j < k; ++j) ds.push_back(atom("eq", {i, z[j]}));
            return all(i, imp(atom("elem", {i, z[k]}), disj(ds)));
        });
    };
    return make("index_cases_" + std::to_string(k), statement, [&](Tac& t) {
        return intro_chain(t, k, [&](const std::vector<std::string>& z, const std::vector<H>& g) {
            return t.all("i", [&](const std::string& i) {
                std::vector<FmP> ds;
                for (size_t j = 0; j < k; ++j) ds.push_back(atom("eq", {i, z[j]}));
                FmP goal = disj(ds);
                return t.assume(atom("elem", {i, z[k]}), [&](H mem) {
                    std::function<H(size_t, H)> go = [&](size_t j, H m) -> H {
                        if (j == 0) return t.p.bottom_elim(t.p.not_elim(t.inst(zero_unfold(t, z[0], g[0]), {i}), m), goal);
                        H s = t.p.iff_l(t.inst(succ_unfold(t, z[j - 1], z[j], g[j]), {i}), m);
                        return t.cases(s, [&](H l) { return go(j - 1, l); }, [&](H r) { return inject(t, r, ds, j - 1); });
                    };
                    return go(k, mem);
                });
            });
        });
    });
}

namespace {

FmP natural(const std::string& n) { return atom("Sys.natural", {n}); }
FmP elem(const std::string& a, const std::string& b) { return atom("elem", {a, b}); }
FmP eqf(const std::string& a, const std::string& b) { return atom("eq", {a, b}); }
FmP le(const std::string& a, const std::string& b) { return disj(elem(a, b), eqf(a, b)); }

}  // namespace

// Ord(x) in the ZF library's encoding, from x natural.
static H ord_of(Tac& t, const std::string& x, H nat) {
    H enc = t.p.iff_l(t.inst(t.p.use("Sys.natural_nat"), {x}), nat);
    return t.mp(t.inst(t.p.use("Nat.nat_into_Ord"), {x}), {enc});
}

std::string Lemmas::nat_cong() {
    return make("nat_cong", [&] {
        std::string n = fresh("_n"), m = fresh("_m");
        return all(n, all(m, imp(eqf(n, m), imp(natural(n), natural(m)))));
    }, [&](Tac& t) {
        return intro_all(t, 2, "x", [&](const std::vector<std::string>& v) {
            return t.assume(eqf(v[0], v[1]), [&](H e) {
                return t.assume(natural(v[0]), [&](H h) {
                    H in_all = t.p.iff_l(t.p.forall_elim(t.p.use("Sys.natural_def"), v[0]), h);
                    H body = t.all("z", [&](const std::string& z) {
                        return t.assume(atom("ind", {z}), [&](H iz) {
                            H nz = t.mp(t.inst(in_all, {z}), {iz});
                            return t.mp(t.inst(t.p.use("elem_first_subst"), {v[0], v[1], z}), {e, nz});
                        });
                    });
                    return t.p.iff_r(t.p.forall_elim(t.p.use("Sys.natural_def"), v[1]), body);
                });
            });
        });
    });
}

std::string Lemmas::natural_succ() {
    return make("natural_succ", [&] {
        std::string n = fresh("_n"), m = fresh("_m");
        return all(n, all(m, imp(natural(n), imp(atom("nsucc", {n, m}), natural(m)))));
    }, [&](Tac& t) {
        return intro_all(t, 2, "x", [&](const std::vector<std::string>& v) {
            const std::string &n = v[0], &m = v[1];
            return t.assume(natural(n), [&](H hn) {
                return t.assume(atom("nsucc", {n, m}), [&](H hs) {
                    H in_all = t.p.iff_l(t.p.forall_elim(t.p.use("Sys.natural_def"), n), hn);
                    H body = t.all("z", [&](const std::string& z) {
                        return t.assume(atom("ind", {z}), [&](H iz) {
                            H nz = t.mp(t.inst(in_all, {z}), {iz});
                            H closed = t.split(t.p.iff_l(t.p.forall_elim(t.p.use("ind_def"), z), iz), 2)[1];
                            return t.obtain(t.mp(t.inst(closed, {n}), {nz}), "s", [&](const std::string& s, H b) {
                                std::vector<H> sb = t.split(b, 2);
                                H ns = t.p.iff_r(t.inst(t.p.use("nsucc_def"), {n, s}), sb[1]);
                                H e = t.mp(t.inst(t.p.use("nsucc_UNIQ"), {n, s, m}), {ns, hs});
                                return t.mp(t.inst(t.p.use("elem_first_subst"), {s, m, z}), {e, sb[0]});
                            });
                        });
                    });
                    return t.p.iff_r(t.p.forall_elim(t.p.use("Sys.natural_def"), m), body);
                });
            });
        });
    });
}

// m in n, from nsucc(m, n).
static H in_succ(Tac& t, const std::string& m, const std::string& n, H hs) {
    H u = t.inst(succ_unfold(t, m, n, hs), {m});
    return t.p.iff_r(u, t.p.or_intro_r(elem(m, m), refl(t, m)));
}

std::string Lemmas::natural_elem() {
    return make("natural_elem", [&] {
        std::string n = fresh("_n"), m = fresh("_m");
        return all(n, all(m, imp(natural(n), imp(elem(m, n), natural(m)))));
    }, [&](Tac& t) {
        return intro_all(t, 2, "x", [&](const std::vector<std::string>& v) {
            const std::string &n = v[0], &m = v[1];
            return t.assume(natural(n), [&](H hn) {
                return t.assume(elem(m, n), [&](H mn) {
                    H lt = t.p.iff_r(t.inst(t.p.use("Ordinal.lt_def"), {m, n}), t.p.and_intro(mn, ord_of(t, n, hn)));
                    H natn = t.p.iff_l(t.inst(t.p.use("Sys.natural_nat"), {n}), hn);
                    H natm = t.mp(t.inst(t.p.use("Nat.lt_nat_in_nat"), {m, n}), {lt, natn});
                    return t.p.iff_r(t.inst(t.p.use("Sys.natural_nat"), {m}), natm);
                });
            });
        });
    });
}

std::string Lemmas::natural_pred() {
    std::string ne = natural_elem();
    return make("natural_pred", [&] {
        std::string m = fresh("_m"), n = fresh("_n");
        return all(m, all(n, imp(natural(n), imp(atom("nsucc", {m, n}), natural(m)))));
    }, [&](Tac& t) {
        return intro_all(t, 2, "x", [&](const std::vector<std::string>& v) {
            const std::string &m = v[0], &n = v[1];
            return t.assume(natural(n), [&](H hn) {
                return t.assume(atom("nsucc", {m, n}), [&](H hs) {
                    return t.mp(t.inst(t.p.use(ne), {n, m}), {hn, in_succ(t, m, n, hs)});
                });
            });
        });
    });
}

std::string Lemmas::trichotomy() {
    return make("trichotomy", [&] {
        std::string m = fresh("_m"), c = fresh("_c");
        return all(m, all(c, imp(natural(m), imp(natural(c), disj({elem(m, c), eqf(m, c), elem(c, m)})))));
    }, [&](Tac& t) {
        return intro_all(t, 2, "x", [&](const std::vector<std::string>& v) {
            return t.assume(natural(v[0]), [&](H hm) {
                return t.assume(natural(v[1]), [&](H hc) {
                    return t.mp(t.inst(t.p.use("Ordinal.Ord_linear"), {v[0], v[1]}), {ord_of(t, v[0], hm), ord_of(t, v[1], hc)});
                });
            });
        });
    });
}

std::string Lemmas::succ_le() {
    std::string ns = natural_succ(), tr = trichotomy();
    return make("succ_le", [&] {
        std::string m = fresh("_m"), c = fresh("_c"), s = fresh("_s");
        return all(m, all(c, all(s, imp(natural(m), imp(natural(c), imp(elem(m, c), imp(atom("nsucc", {m, s}), le(s, c))))))));
    }, [&](Tac& t) {
        return intro_all(t, 3, "x", [&](const std::vector<std::string>& v) {
            const std::string &m = v[0], &c = v[1], &s = v[2];
            FmP goal = le(s, c);
            return t.assume(natural(m), [&](H hm) {
                return t.assume(natural(c), [&](H hc) {
                    return t.assume(elem(m, c), [&](H mc) {
                        return t.assume(atom("nsucc", {m, s}), [&](H hs) {
                            H nat_s = t.mp(t.inst(t.p.use(ns), {m, s}), {hm, hs});
                            H three = t.mp(t.inst(t.p.use(tr), {s, c}), {nat_s, hc});
                            return t.cases(three, 3, [&](size_t k, H h) -> H {
                                if (k == 0) return t.p.or_intro_l(h, eqf(s, c));
                                if (k == 1) return t.p.or_intro_r(elem(s, c), h);
                                H d = t.p.iff_l(t.inst(succ_unfold(t, m, s, hs), {c}), h);
                                return t.cases(d, [&](H cm) {
                                    H cc = t.mp(t.inst(t.p.use("Ordinal.Ord_trans"), {c, m, c}), {cm, mc, ord_of(t, c, hc)});
                                    return t.p.bottom_elim(t.p.not_elim(t.inst(t.p.use("no_self_member"), {c}), cc), goal);
                                }, [&](H ecm) {
                                    H cc = t.mp(t.inst(t.p.use("elem_first_subst"), {m, c, c}), {t.p.eq_sym(ecm), mc});
                                    return t.p.bottom_elim(t.p.not_elim(t.inst(t.p.use("no_self_member"), {c}), cc), goal);
                                });
                            });
                        });
                    });
                });
            });
        });
    });
}

std::string Lemmas::pred_le() {
    return make("pred_le", [&] {
        std::string m = fresh("_m"), n = fresh("_n"), c = fresh("_c");
        return all(m, all(n, all(c, imp(natural(c), imp(atom("nsucc", {m, n}), imp(le(n, c), le(m, c)))))));
    }, [&](Tac& t) {
        return intro_all(t, 3, "x", [&](const std::vector<std::string>& v) {
            const std::string &m = v[0], &n = v[1], &c = v[2];
            return t.assume(natural(c), [&](H hc) {
                return t.assume(atom("nsucc", {m, n}), [&](H hs) {
                    return t.assume(le(n, c), [&](H hle) {
                        H mn = in_succ(t, m, n, hs);
                        return t.cases(hle, [&](H nc) {
                            H mc = t.mp(t.inst(t.p.use("Ordinal.Ord_trans"), {m, n, c}), {mn, nc, ord_of(t, c, hc)});
                            return t.p.or_intro_l(mc, eqf(m, c));
                        }, [&](H enc) {
                            H mc = t.mp(t.inst(t.p.use("elem_second"), {n, c, m}), {enc, mn});
                            return t.p.or_intro_l(mc, eqf(m, c));
                        });
                    });
                });
            });
        });
    });
}

std::string Lemmas::natural_zero() {
    return make("natural_zero", [&] {
        std::string z = fresh("_z");
        return all(z, imp(atom("zero", {z}), natural(z)));
    }, [&](Tac& t) {
        return intro_all(t, 1, "x", [&](const std::vector<std::string>& v) {
            const std::string& z = v[0];
            return t.assume(atom("zero", {z}), [&](H hz) {
                H in_all = t.all("w", [&](const std::string& w) {
                    return t.assume(atom("ind", {w}), [&](H iw) {
                        H has0 = t.split(t.p.iff_l(t.p.forall_elim(t.p.use("ind_def"), w), iw), 2)[0];
                        return t.obtain(has0, "e", [&](const std::string& e, H b) {
                            std::vector<H> eb = t.split(b, 2);
                            H ze = t.p.iff_r(t.p.forall_elim(t.p.use("zero_def"), e), eb[1]);
                            H eq = t.mp(t.inst(t.p.use("zero_UNIQ"), {e, z}), {ze, hz});
                            return t.mp(t.inst(t.p.use("elem_first_subst"), {e, z, w}), {eq, eb[0]});
                        });
                    });
                });
                return t.p.iff_r(t.p.forall_elim(t.p.use("Sys.natural_def"), z), in_all);
            });
        });
    });
}

std::string Lemmas::zero_le() {
    std::string tr = trichotomy(), nz = natural_zero();
    return make("zero_le", [&] {
        std::string z = fresh("_z"), c = fresh("_c");
        return all(z, all(c, imp(atom("zero", {z}), imp(natural(c), le(z, c)))));
    }, [&](Tac& t) {
        return intro_all(t, 2, "x", [&](const std::vector<std::string>& v) {
            const std::string &z = v[0], &c = v[1];
            FmP goal = le(z, c);
            return t.assume(atom("zero", {z}), [&](H hz) {
                return t.assume(natural(c), [&](H hc) {
                    H nat_z = t.mp(t.inst(t.p.use(nz), {z}), {hz});
                    H three = t.mp(t.inst(t.p.use(tr), {z, c}), {nat_z, hc});
                    return t.cases(three, 3, [&](size_t k, H h) -> H {
                        if (k == 0) return t.p.or_intro_l(h, eqf(z, c));
                        if (k == 1) return t.p.or_intro_r(elem(z, c), h);
                        H none = t.inst(zero_unfold(t, z, hz), {c});
                        return t.p.bottom_elim(t.p.not_elim(none, h), goal);
                    });
                });
            });
        });
    });
}

std::string Lemmas::len_uniq() {
    return make("len_uniq", [&] {
        std::string x = fresh("_t"), n = fresh("_n"), m = fresh("_m");
        return all(x, all(n, all(m, imp(atom("tuple", {x, n}), imp(atom("tuple", {x, m}), eqf(n, m))))));
    }, [&](Tac& t) {
        return intro_all(t, 3, "x", [&](const std::vector<std::string>& v) {
            const std::string &x = v[0], &n = v[1], &m = v[2];
            return t.assume(atom("tuple", {x, n}), [&](H tn) {
                return t.assume(atom("tuple", {x, m}), [&](H tm) {
                    auto into = [&](H from, const std::string& a, H to_t, const std::string& b) {
                        return [&, from, a, to_t, b](const std::string& u) {
                            return t.assume(elem(u, a), [&](H ua) {
                                H has = t.split(t.p.iff_l(t.inst(t.p.use("tuple_def"), {x, a}), from), 4)[2];
                                return t.obtain(t.mp(t.inst(has, {u}), {ua}), "y", [&](const std::string& y, H py) {
                                    return t.mp(t.inst(t.mp(t.inst(t.p.use("tuple_dom"), {x, b}), {to_t}), {u, y}), {py});
                                });
                            });
                        };
                    };
                    H ext = t.all("u", [&](const std::string& u) {
                        return t.p.iff_intro(into(tn, n, tm, m)(u), into(tm, m, tn, n)(u));
                    });
                    return t.p.iff_r(t.inst(t.p.use("extensionality"), {n, m}), ext);
                });
            });
        });
    });
}

std::string Lemmas::pmem_cong3() {
    return make("pmem_cong3", [&] {
        std::string i = fresh("_i"), y = fresh("_y"), r = fresh("_r"), r2 = fresh("_r");
        return all(i, all(y, all(r, all(r2, imp(eqf(r, r2), imp(atom("pmem", {i, y, r}), atom("pmem", {i, y, r2})))))));
    }, [&](Tac& t) {
        return intro_all(t, 4, "x", [&](const std::vector<std::string>& v) {
            const std::string &i = v[0], &y = v[1], &r = v[2], &r2 = v[3];
            return t.assume(eqf(r, r2), [&](H e) {
                return t.assume(atom("pmem", {i, y, r}), [&](H h) {
                    H pd = t.p.iff_l(t.inst(t.p.use("pmem_def"), {i, y, r}), h);
                    return t.obtain(pd, "p", [&](const std::string& p, H b) {
                        std::vector<H> kp = t.split(b, 2);
                        H ep = t.mp(t.inst(t.p.use("elem_second"), {r, r2, p}), {e, kp[1]});
                        H w = t.witness(t.p.and_intro(kp[0], ep), p);
                        return t.p.iff_r(t.inst(t.p.use("pmem_def"), {i, y, r2}), w);
                    });
                });
            });
        });
    });
}

std::string Lemmas::pmem_cong2() {
    return make("pmem_cong2", [&] {
        std::string i = fresh("_i"), y = fresh("_y"), y2 = fresh("_y"), r = fresh("_r");
        return all(i, all(y, all(y2, all(r, imp(eqf(y, y2), imp(atom("pmem", {i, y, r}), atom("pmem", {i, y2, r})))))));
    }, [&](Tac& t) {
        return intro_all(t, 4, "x", [&](const std::vector<std::string>& v) {
            const std::string &i = v[0], &y = v[1], &y2 = v[2], &r = v[3];
            return t.assume(eqf(y, y2), [&](H e) {
                return t.assume(atom("pmem", {i, y, r}), [&](H h) {
                    H pd = t.p.iff_l(t.inst(t.p.use("pmem_def"), {i, y, r}), h);
                    return t.obtain(pd, "p", [&](const std::string& p, H b) {
                        std::vector<H> kp = t.split(b, 2);
                        H k2 = t.mp(t.inst(t.p.use("kpair_arg_cong"), {i, y, i, y2, p}), {kp[0], refl(t, i), e});
                        H w = t.witness(t.p.and_intro(k2, kp[1]), p);
                        return t.p.iff_r(t.inst(t.p.use("pmem_def"), {i, y2, r}), w);
                    });
                });
            });
        });
    });
}

std::string Lemmas::tuple_cong1() {
    std::string pc = pmem_cong3();
    return make("tuple_cong1", [&] {
        std::string x = fresh("_t"), x2 = fresh("_t"), n = fresh("_n");
        return all(x, all(x2, all(n, imp(eqf(x, x2), imp(atom("tuple", {x, n}), atom("tuple", {x2, n}))))));
    }, [&](Tac& t) {
        return intro_all(t, 3, "x", [&](const std::vector<std::string>& v) {
            const std::string &x = v[0], &x2 = v[1], &n = v[2];
            return t.assume(eqf(x, x2), [&](H e) {
                return t.assume(atom("tuple", {x, n}), [&](H ht) {
                    std::vector<H> td = t.split(t.p.iff_l(t.inst(t.p.use("tuple_def"), {x, n}), ht), 4);
                    H back = t.p.eq_sym(e);
                    H a = t.all("u", [&](const std::string& u) {
                        return t.assume(elem(u, x2), [&](H hu) {
                            return t.mp(t.inst(td[1], {u}), {t.mp(t.inst(t.p.use("elem_second"), {x2, x, u}), {back, hu})});
                        });
                    });
                    H b = t.all("i", [&](const std::string& i) {
                        return t.assume(elem(i, n), [&](H hi) {
                            return t.obtain(t.mp(t.inst(td[2], {i}), {hi}), "y", [&](const std::string& y, H py) {
                                H p2 = t.mp(t.inst(t.p.use(pc), {i, y, x, x2}), {e, py});
                                return t.witness(p2, y);
                            });
                        });
                    });
                    H c = t.all("i", [&](const std::string& i) {
                        return t.all("y", [&](const std::string& y) {
                            return t.all("z", [&](const std::string& z) {
                                return t.assume(atom("pmem", {i, y, x2}), [&](H py) {
                                    return t.assume(atom("pmem", {i, z, x2}), [&](H pz) {
                                        H py1 = t.mp(t.inst(t.p.use(pc), {i, y, x2, x}), {back, py});
                                        H pz1 = t.mp(t.inst(t.p.use(pc), {i, z, x2, x}), {back, pz});
                                        return t.mp(t.inst(td[3], {i, y, z}), {py1, pz1});
                                    });
                                });
                            });
                        });
                    });
                    return t.p.iff_r(t.inst(t.p.use("tuple_def"), {x2, n}), t.join({td[0], a, b, c}));
                });
            });
        });
    });
}

std::string Lemmas::pair_pow() {
    return make("pair_pow", [&] {
        std::string i = fresh("_i"), y = fresh("_y"), v = fresh("_v"), w = fresh("_w"), p1 = fresh("_p"), p2 = fresh("_p");
        return all_of({i, y, v, w, p1, p2},
                      imp(atom("kpair", {i, y, v}), imp(elem(i, w), imp(elem(y, w), imp(atom("Pow", {w, p1}),
                          imp(atom("Pow", {p1, p2}), elem(v, p2)))))));
    }, [&](Tac& t) {
        return intro_all(t, 6, "x", [&](const std::vector<std::string>& vs) {
            const std::string &i = vs[0], &y = vs[1], &v = vs[2], &W = vs[3], &p1 = vs[4], &p2 = vs[5];
            return t.assume(atom("kpair", {i, y, v}), [&](H ky) {
                return t.assume(elem(i, W), [&](H iW) {
                    return t.assume(elem(y, W), [&](H yW) {
                        return t.assume(atom("Pow", {W, p1}), [&](H h1) {
                            return t.assume(atom("Pow", {p1, p2}), [&](H h2) {
                                H u1 = t.p.iff_l(t.inst(t.p.use("Pow_def"), {W, p1}), h1);
                                H u2 = t.p.iff_l(t.inst(t.p.use("Pow_def"), {p1, p2}), h2);
                                auto into_w = [&](const std::string& from, H eqzf, const std::string& z) {
                                    return t.mp(t.inst(t.p.use("elem_first_subst"), {from, z, W}),
                                                {t.p.eq_sym(eqzf), from == i ? iW : yW});
                                };
                                H in_p1 = t.all("w", [&](const std::string& w) {
                                    return t.assume(elem(w, v), [&](H hw) {
                                        H kd = t.p.iff_l(t.inst(t.p.use("kpair_def"), {i, y, v}), ky);
                                        return t.obtain(kd, "a", [&](const std::string& a, H ra) {
                                            return t.obtain(ra, "b", [&](const std::string& b2, H rb) {
                                                std::vector<H> us = t.split(rb, 3);
                                                H wc = t.mp(t.inst(t.p.use("upair_elem"), {a, b2, v, w}), {us[2], hw});
                                                H mem = t.all("z", [&](const std::string& z) {
                                                    return t.assume(elem(z, w), [&](H hz) {
                                                        return t.cases(wc, [&](H wa) {
                                                            H za = t.mp(t.inst(t.p.use("elem_second"), {w, a, z}), {wa, hz});
                                                            return into_w(i, t.mp(t.inst(t.p.use("sing_elem"), {i, a, z}), {us[0], za}), z);
                                                        }, [&](H wb) {
                                                            H zb = t.mp(t.inst(t.p.use("elem_second"), {w, b2, z}), {wb, hz});
                                                            H c2 = t.mp(t.inst(t.p.use("upair_elem"), {i, y, b2, z}), {us[1], zb});
                                                            return t.cases(c2, [&](H zi) { return into_w(i, zi, z); },
                                                                           [&](H zy) { return into_w(y, zy, z); });
                                                        });
                                                    });
                                                });
                                                return t.p.iff_r(t.inst(u1, {w}), mem);
                                            });
                                        });
                                    });
                                });
                                return t.p.iff_r(t.inst(u2, {v}), in_p1);
                            });
                        });
                    });
                });
            });
        });
    });
}

std::string Lemmas::tuple_pow() {
    std::string pp = pair_pow();
    auto statement = [&] {
        std::string x = fresh("_t"), n = fresh("_n"), w = fresh("_w"), p1 = fresh("_p"), p2 = fresh("_p"), p3 = fresh("_p");
        std::string i = fresh("_i"), i2 = fresh("_i"), y = fresh("_y");
        FmP idx = all(i, imp(atom("elem", {i, n}), atom("elem", {i, w})));
        FmP ent = all(i2, all(y, imp(atom("pmem", {i2, y, x}), atom("elem", {y, w}))));
        FmP body = imp(atom("tuple", {x, n}),
                       imp(idx, imp(ent, imp(atom("Pow", {w, p1}), imp(atom("Pow", {p1, p2}), imp(atom("Pow", {p2, p3}), atom("elem", {x, p3})))))));
        return all_of({x, n, w, p1, p2, p3}, body);
    };
    return make("tuple_pow", statement, [&](Tac& t) {
        return intro_all(t, 6, "x", [&](const std::vector<std::string>& vs) {
            const std::string &x = vs[0], &n = vs[1], &W = vs[2], &p1 = vs[3], &p2 = vs[4], &p3 = vs[5];
            std::string i0 = fresh("_i"), i2 = fresh("_i"), y0 = fresh("_y");
            FmP idx = all(i0, imp(atom("elem", {i0, n}), atom("elem", {i0, W})));
            FmP ent = all(i2, all(y0, imp(atom("pmem", {i2, y0, x}), atom("elem", {y0, W}))));
            return t.assume(atom("tuple", {x, n}), [&](H ht) {
                return t.assume(idx, [&](H hidx) {
                    return t.assume(ent, [&](H hent) {
                        return t.assume(atom("Pow", {W, p1}), [&](H h1) {
                            return t.assume(atom("Pow", {p1, p2}), [&](H h2) {
                                return t.assume(atom("Pow", {p2, p3}), [&](H h3) {
                                    auto pow = [&](const std::string& a, const std::string& r, H h) {
                                        return t.p.iff_l(t.inst(t.p.use("Pow_def"), {a, r}), h);
                                    };
                                    H u3 = pow(p2, p3, h3);
                                    H parts = t.split(t.p.iff_l(t.inst(t.p.use("tuple_def"), {x, n}), ht), 4)[1];
                                    H sub = t.all("v", [&](const std::string& v) {
                                        return t.assume(atom("elem", {v, x}), [&](H hv) {
                                            H ex = t.mp(t.inst(parts, {v}), {hv});
                                            return t.obtain(ex, "i", [&](const std::string& i, H b) {
                                                std::vector<H> iy = t.split(b, 2);
                                                return t.obtain(iy[1], "y", [&](const std::string& y, H ky) {
                                                    H py = t.p.iff_r(t.mp(t.inst(t.p.use("pmem_at"), {i, y, v, x}), {ky}), hv);
                                                    H yW = t.mp(t.inst(hent, {i, y}), {py});
                                                    H iW = t.mp(t.inst(hidx, {i}), {iy[0]});
                                                    return t.mp(t.inst(t.p.use(pp), {i, y, v, W, p1, p2}), {ky, iW, yW, h1, h2});
                                                });
                                            });
                                        });
                                    });
                                    return t.p.iff_r(t.inst(u3, {x}), sub);
                                });
                            });
                        });
                    });
                });
            });
        });
    });
}

std::string Lemmas::natural_index() {
    return make("natural_index", [&] {
        std::string n = fresh("_n");
        return all(n, imp(natural(n), atom("index", {n})));
    }, [&](Tac& t) {
        return intro_all(t, 1, "x", [&](const std::vector<std::string>& v) {
            const std::string& n = v[0];
            return t.assume(natural(n), [&](H hn) {
                H ord = ord_of(t, n, hn);
                H trans = t.all("x", [&](const std::string& x) {
                    return t.assume(elem(x, n), [&](H xn) {
                        return t.all("y", [&](const std::string& y) {
                            return t.assume(elem(y, x), [&](H yx) {
                                return t.mp(t.inst(t.p.use("Ordinal.Ord_trans"), {y, x, n}), {yx, xn, ord});
                            });
                        });
                    });
                });
                H self = t.inst(t.p.use("no_self_member"), {n});
                return t.p.iff_r(t.p.forall_elim(t.p.use("index_def"), n), t.p.and_intro(trans, self));
            });
        });
    });
}

std::string Lemmas::nsucc_cong2() {
    return make("nsucc_cong2", [&] {
        std::string n = fresh("_n"), m = fresh("_m"), m2 = fresh("_m");
        return all(n, all(m, all(m2, imp(eqf(m, m2), imp(atom("nsucc", {n, m}), atom("nsucc", {n, m2}))))));
    }, [&](Tac& t) {
        return intro_all(t, 3, "x", [&](const std::vector<std::string>& v) {
            const std::string &n = v[0], &m = v[1], &m2 = v[2];
            return t.assume(eqf(m, m2), [&](H e) {
                return t.assume(atom("nsucc", {n, m}), [&](H hs) {
                    H u = succ_unfold(t, n, m, hs);
                    H body = t.all("u", [&](const std::string& x) {
                        H a = t.inst(u, {x});
                        H cr = t.mp(t.inst(t.p.use("cong_elem_r"), {x, m, m2}), {e});
                        H l = t.assume(elem(x, m2), [&](H h) { return t.p.iff_l(a, t.p.iff_r(cr, h)); });
                        H r = t.assume(t.p.fm(a)->b, [&](H h) { return t.p.iff_l(cr, t.p.iff_r(a, h)); });
                        return t.p.iff_intro(l, r);
                    });
                    return t.p.iff_r(t.inst(t.p.use("nsucc_def"), {n, m2}), body);
                });
            });
        });
    });
}

std::string Lemmas::zero_or_succ(const std::string& cases) {
    return make("zero_or_succ", [&] {
        std::string n = fresh("_n"), m = fresh("_m");
        return all(n, imp(natural(n), disj(atom("zero", {n}), some(m, atom("nsucc", {m, n})))));
    }, [&](Tac& t) {
        return intro_all(t, 1, "x", [&](const std::vector<std::string>& v) {
            const std::string& n = v[0];
            return t.assume(natural(n), [&](H hn) {
                return t.obtain(t.p.use("infinity"), "z", [&](const std::string& z, H iz) {
                    std::vector<H> zp = t.split(iz, 2);
                    return t.obtain(t.inst(t.p.use(cases), {z}), "C", [&](const std::string& C, H cw) {
                        auto phi = [&](const std::string& w) { return t.p.fm(t.inst(cw, {w}))->b->b; };
                        FmP rhs = t.p.fm(t.p.forall_elim(t.p.use("ind_def"), C))->b;
                        H has0 = t.obtain(zp[0], "e", [&](const std::string& e, H eb) {
                            std::vector<H> ez = t.split(eb, 2);
                            H ze = t.p.iff_r(t.p.forall_elim(t.p.use("zero_def"), e), ez[1]);
                            H eC = t.p.iff_r(t.inst(cw, {e}), t.p.and_intro(ez[0], t.p.or_intro_l(ze, phi(e)->b)));
                            return t.witness(rhs->a, e, t.p.and_intro(eC, ez[1]));
                        });
                        H closed = t.all("y", [&](const std::string& y) {
                            return t.assume(elem(y, C), [&](H yC) {
                                std::vector<H> yb = t.split(t.p.iff_l(t.inst(cw, {y}), yC), 2);
                                std::string s0 = fresh("_s"), w0 = fresh("_w");
                                FmP target = some(s0, conj(elem(s0, C), all(w0, iff(elem(w0, s0), disj(elem(w0, y), eqf(w0, y))))));
                                return t.obtain(t.mp(t.inst(zp[1], {y}), {yb[0]}), "s", [&](const std::string& s, H sb) {
                                    std::vector<H> ss = t.split(sb, 2);
                                    H ns = t.p.iff_r(t.inst(t.p.use("nsucc_def"), {y, s}), ss[1]);
                                    FmP ph = phi(s);
                                    H sC = t.p.iff_r(t.inst(cw, {s}), t.p.and_intro(ss[0], t.p.or_intro_r(ph->a, t.witness(ph->b, y, ns))));
                                    return t.witness(target, s, t.p.and_intro(sC, ss[1]));
                                });
                            });
                        });
                        H indC = t.p.iff_r(t.p.forall_elim(t.p.use("ind_def"), C), t.p.and_intro(has0, closed));
                        H nC = t.mp(t.inst(t.p.iff_l(t.p.forall_elim(t.p.use("Sys.natural_def"), n), hn), {C}), {indC});
                        return t.p.and_r(t.p.iff_l(t.inst(cw, {n}), nC));
                    });
                });
            });
        });
    });
}

std::string Lemmas::empty_tuple() {
    return make("empty_tuple", [&] {
        std::string v = fresh("_t"), n = fresh("_n");
        return all(v, all(n, imp(atom("tuple", {v, n}), imp(atom("zero", {n}), atom("zero", {v})))));
    }, [&](Tac& t) {
        return intro_all(t, 2, "x", [&](const std::vector<std::string>& vs) {
            const std::string &v = vs[0], &n = vs[1];
            return t.assume(atom("tuple", {v, n}), [&](H tv) {
                return t.assume(atom("zero", {n}), [&](H zn) {
                    H dom = t.split(t.p.iff_l(t.inst(t.p.use("tuple_def"), {v, n}), tv), 4)[1];
                    H none = t.all("u", [&](const std::string& u) {
                        return t.refute(elem(u, v), [&](H uv) {
                            return t.obtain(t.mp(t.inst(dom, {u}), {uv}), "i", [&](const std::string& i, H b) {
                                return t.p.not_elim(t.inst(zero_unfold(t, n, zn), {i}), t.split(b, 2)[0]);
                            });
                        });
                    });
                    return t.p.iff_r(t.p.forall_elim(t.p.use("zero_def"), v), none);
                });
            });
        });
    });
}

std::string Lemmas::first_ex() {
    std::string zl = zero_le(), nc = num_cong(0), pc = pmem_cong1();
    return make("first_ex", [&] {
        std::string v = fresh("_t"), n = fresh("_n"), y = fresh("_y");
        return all(v, all(n, imp(atom("tuple", {v, n}), imp(natural(n), imp(neg(atom("zero", {n})), some(y, enc::at(0, y, v)))))));
    }, [&](Tac& t) {
        return intro_all(t, 2, "x", [&](const std::vector<std::string>& vs) {
            const std::string &v = vs[0], &n = vs[1];
            std::string y0 = fresh("_y");
            FmP goal = some(y0, enc::at(0, y0, v));
            return t.assume(atom("tuple", {v, n}), [&](H tv) {
                return t.assume(natural(n), [&](H hn) {
                    return t.assume(neg(atom("zero", {n})), [&](H nz) {
                        return t.obtain(t.p.use("zero_EX"), "z", [&](const std::string& z, H hz) {
                            H le0 = t.mp(t.inst(t.p.use(zl), {z, n}), {hz, hn});
                            return t.cases(le0, [&](H zn) {
                                H has = t.split(t.p.iff_l(t.inst(t.p.use("tuple_def"), {v, n}), tv), 4)[2];
                                return t.obtain(t.mp(t.inst(has, {z}), {zn}), "y", [&](const std::string& y, H py) {
                                    H at = intro_chain(t, 0, [&](const std::vector<std::string>& w, const std::vector<H>& g) {
                                        H e = t.mp(t.inst(t.p.use("zero_UNIQ"), {z, w[0]}), {hz, g[0]});
                                        return t.mp(t.inst(t.p.use(pc), {z, w[0], y, v}), {e, py});
                                    });
                                    return t.witness(goal, y, at);
                                });
                            }, [&](H ezn) {
                                H zn2 = t.mp(t.inst(t.p.use(nc), {z, n}), {ezn, hz});
                                return t.p.bottom_elim(t.p.not_elim(nz, zn2), goal);
                            });
                        });
                    });
                });
            });
        });
    });
}

std::string Lemmas::rest_ex(const std::string& pairs) {
    std::string pp = pair_pow(), np = natural_pred(), ni = natural_index(), ne = natural_elem(), sl = succ_le();
    std::string p1c = pmem_cong1(), p2c = pmem_cong2();
    auto shifted = [](const std::string& v, const std::string& r) {
        std::string i = fresh("_i"), j = fresh("_j"), y = fresh("_y");
        return all(i, all(j, imp(atom("nsucc", {i, j}), all(y, iff(atom("pmem", {j, y, v}), atom("pmem", {i, y, r}))))));
    };
    return make("rest_ex", [&] {
        std::string v = fresh("_t"), n = fresh("_n"), m = fresh("_m"), r = fresh("_r");
        return all(v, all(n, all(m, imp(atom("tuple", {v, n}), imp(atom("nsucc", {m, n}), imp(natural(n),
                   some(r, conj(atom("tuple", {r, m}), shifted(v, r)))))))));
    }, [&](Tac& t) {
        return intro_all(t, 3, "x", [&](const std::vector<std::string>& vs) {
            const std::string &v = vs[0], &n = vs[1], &m = vs[2];
            std::string r0 = fresh("_r");
            FmP goal = some(r0, conj(atom("tuple", {r0, m}), shifted(v, r0)));
            return t.assume(atom("tuple", {v, n}), [&](H tv) {
                return t.assume(atom("nsucc", {m, n}), [&](H hs) {
                    return t.assume(natural(n), [&](H hn) {
                        H natm = t.mp(t.inst(t.p.use(np), {m, n}), {hn, hs});
                        std::vector<H> td = t.split(t.p.iff_l(t.inst(t.p.use("tuple_def"), {v, n}), tv), 4);
                        // W = n with v's entries, the union of the union of v holding each entry.
                        return t.obtain(t.inst(t.p.use("union"), {v}), "U", [&](const std::string& u1, H d1) {
                        return t.obtain(t.inst(t.p.use("union"), {u1}), "U", [&](const std::string& u2, H d2) {
                        return t.obtain(t.inst(t.p.use("union2_ex"), {n, u2}), "W", [&](const std::string& W, H dw) {
                        return t.obtain(t.inst(t.p.use("Pow_EX"), {W}), "P", [&](const std::string& p1, H h1) {
                        return t.obtain(t.inst(t.p.use("Pow_EX"), {p1}), "P", [&](const std::string& p2, H h2) {
                        return t.obtain(t.inst(t.p.use(pairs), {v, p2}), "C", [&](const std::string& C, H cw) {
                            auto in_w = [&](const std::string& x, H side, bool left) {
                                H u = t.inst(dw, {x});
                                FmP d = t.p.fm(u)->b;
                                return t.p.iff_r(u, left ? t.p.or_intro_l(side, d->b) : t.p.or_intro_r(d->a, side));
                            };
                            auto entry_in = [&](const std::string& j, const std::string& y, H pjy) {
                                H pd = t.p.iff_l(t.inst(t.p.use("pmem_def"), {j, y, v}), pjy);
                                return t.obtain(pd, "p", [&](const std::string& p, H pb) {
                                    std::vector<H> kp = t.split(pb, 2);
                                    H kd = t.p.iff_l(t.inst(t.p.use("kpair_def"), {j, y, p}), kp[0]);
                                    return t.obtain(kd, "a", [&](const std::string& a, H ra) {
                                        return t.obtain(ra, "b", [&](const std::string& b, H rb) {
                                            std::vector<H> us = t.split(rb, 3);
                                            H bp = t.mp(t.inst(t.p.use("upair_mem2"), {a, b, p}), {us[2]});
                                            H b1 = t.inst(d1, {b});
                                            H bU = t.p.iff_r(b1, t.witness(t.p.fm(b1)->b, p, t.p.and_intro(kp[1], bp)));
                                            H yb = t.mp(t.inst(t.p.use("upair_mem2"), {j, y, b}), {us[1]});
                                            H y2 = t.inst(d2, {y});
                                            H yU = t.p.iff_r(y2, t.witness(t.p.fm(y2)->b, b, t.p.and_intro(bU, yb)));
                                            return in_w(y, yU, false);
                                        });
                                    });
                                });
                            };
                            auto phi = [&](const std::string& w) { return t.p.fm(t.inst(cw, {w}))->b->b; };
                            auto inside = [](const FmP& ex, const std::string& x) { return subst(ex->a->b, {{ex->name, x}}); };
                            H ordn = ord_of(t, n, hn), ordm = ord_of(t, m, natm);
                            H shift = t.all("i", [&](const std::string& i) {
                                return t.all("j", [&](const std::string& j) {
                                    return t.assume(atom("nsucc", {i, j}), [&](H nij) {
                                        return t.all("y", [&](const std::string& y) {
                                            H to = t.assume(atom("pmem", {j, y, v}), [&](H pjy) {
                                                H jn = t.mp(t.inst(t.mp(t.inst(t.p.use("tuple_dom"), {v, n}), {tv}), {j, y}), {pjy});
                                                H in_n = t.mp(t.inst(t.p.use("Ordinal.Ord_trans"), {i, j, n}), {in_succ(t, i, j, nij), jn, ordn});
                                                H iW = in_w(i, in_n, true), yW = entry_in(j, y, pjy);
                                                return t.obtain(t.inst(t.p.use("pair_ex"), {i, y}), "p", [&](const std::string& p, H kp) {
                                                    H pin = t.mp(t.inst(t.p.use(pp), {i, y, p, W, p1, p2}), {kp, iW, yW, h1, h2});
                                                    FmP ph = phi(p), ty = inside(ph, i), tj = inside(ty, y)->b;
                                                    H hj = t.witness(tj, j, t.p.and_intro(nij, pjy));
                                                    H hi = t.witness(ph, i, t.witness(ty, y, t.p.and_intro(kp, hj)));
                                                    H pC = t.p.iff_r(t.inst(cw, {p}), t.p.and_intro(pin, hi));
                                                    return t.p.iff_r(t.mp(t.inst(t.p.use("pmem_at"), {i, y, p, C}), {kp}), pC);
                                                });
                                            });
                                            H back = t.assume(atom("pmem", {i, y, C}), [&](H piy) {
                                                H pd = t.p.iff_l(t.inst(t.p.use("pmem_def"), {i, y, C}), piy);
                                                return t.obtain(pd, "p", [&](const std::string& p, H pb) {
                                                    std::vector<H> kp = t.split(pb, 2);
                                                    H ph = t.p.and_r(t.p.iff_l(t.inst(cw, {p}), kp[1]));
                                                    return t.obtain(ph, "i", [&](const std::string& i2, H b1) {
                                                        return t.obtain(b1, "y", [&](const std::string& y2, H b2) {
                                                            std::vector<H> kj = t.split(b2, 2);
                                                            std::vector<H> inj = t.split(t.mp(t.inst(t.p.use("pair_inj"), {i2, y2, i, y, p}), {kj[0], kp[0]}), 2);
                                                            return t.obtain(kj[1], "j", [&](const std::string& j2, H b3) {
                                                                std::vector<H> sp = t.split(b3, 2);
                                                                H ejj = t.mp(t.inst(t.p.use("nsucc_eq"), {i2, i, j2, j}), {inj[0], sp[0], nij});
                                                                H pj = t.mp(t.inst(t.p.use(p1c), {j2, j, y2, v}), {ejj, sp[1]});
                                                                return t.mp(t.inst(t.p.use(p2c), {j, y2, y, v}), {inj[1], pj});
                                                            });
                                                        });
                                                    });
                                                });
                                            });
                                            return t.p.iff_intro(to, back);
                                        });
                                    });
                                });
                            });
                            H idx = t.mp(t.inst(t.p.use(ni), {m}), {natm});
                            H pairs_in = t.all("x", [&](const std::string& x) {
                                return t.assume(elem(x, C), [&](H xC) {
                                    std::string i0 = fresh("_i"), y0 = fresh("_y");
                                    FmP target = some(i0, conj(elem(i0, m), some(y0, atom("kpair", {i0, y0, x}))));
                                    H ph = t.p.and_r(t.p.iff_l(t.inst(cw, {x}), xC));
                                    return t.obtain(ph, "i", [&](const std::string& i, H b1) {
                                        return t.obtain(b1, "y", [&](const std::string& y, H b2) {
                                            std::vector<H> kj = t.split(b2, 2);
                                            return t.obtain(kj[1], "j", [&](const std::string& j, H b3) {
                                                std::vector<H> sp = t.split(b3, 2);
                                                H jn = t.mp(t.inst(t.mp(t.inst(t.p.use("tuple_dom"), {v, n}), {tv}), {j, y}), {sp[1]});
                                                H d = t.p.iff_l(t.inst(succ_unfold(t, m, n, hs), {j}), jn);
                                                H ij = in_succ(t, i, j, sp[0]);
                                                H im = t.cases(d, [&](H jm) {
                                                    return t.mp(t.inst(t.p.use("Ordinal.Ord_trans"), {i, j, m}), {ij, jm, ordm});
                                                }, [&](H ejm) { return t.mp(t.inst(t.p.use("elem_second"), {j, m, i}), {ejm, ij}); });
                                                FmP ty = inside(target, i)->b;
                                                return t.witness(target, i, t.p.and_intro(im, t.witness(ty, y, kj[0])));
                                            });
                                        });
                                    });
                                });
                            });
                            H has = t.all("i", [&](const std::string& i) {
                                return t.assume(elem(i, m), [&](H im) {
                                    std::string y0 = fresh("_y");
                                    FmP target = some(y0, atom("pmem", {i, y0, C}));
                                    H nati = t.mp(t.inst(t.p.use(ne), {m, i}), {natm, im});
                                    return t.obtain(t.inst(t.p.use("nsucc_EX"), {i}), "j", [&](const std::string& j, H nij) {
                                        H jle = t.mp(t.inst(t.p.use(sl), {i, m, j}), {nati, natm, im, nij});
                                        H jn = t.p.iff_r(t.inst(succ_unfold(t, m, n, hs), {j}), jle);
                                        return t.obtain(t.mp(t.inst(td[2], {j}), {jn}), "y", [&](const std::string& y, H pjy) {
                                            H at = t.mp(t.inst(shift, {i, j}), {nij});
                                            return t.witness(target, y, t.p.iff_l(t.inst(at, {y}), pjy));
                                        });
                                    });
                                });
                            });
                            H fun = t.all("i", [&](const std::string& i) {
                                return t.all("y", [&](const std::string& y) {
                                    return t.all("z", [&](const std::string& z) {
                                        return t.assume(atom("pmem", {i, y, C}), [&](H piy) {
                                            return t.assume(atom("pmem", {i, z, C}), [&](H piz) {
                                                return t.obtain(t.inst(t.p.use("nsucc_EX"), {i}), "j", [&](const std::string& j, H nij) {
                                                    H at = t.mp(t.inst(shift, {i, j}), {nij});
                                                    H pjy = t.p.iff_r(t.inst(at, {y}), piy), pjz = t.p.iff_r(t.inst(at, {z}), piz);
                                                    return t.mp(t.inst(td[3], {j, y, z}), {pjy, pjz});
                                                });
                                            });
                                        });
                                    });
                                });
                            });
                            H tC = t.p.iff_r(t.inst(t.p.use("tuple_def"), {C, m}), t.join({idx, pairs_in, has, fun}));
                            return t.witness(goal, C, t.p.and_intro(tC, shift));
                        });
                        });
                        });
                        });
                        });
                        });
                    });
                });
            });
        });
    });
}

namespace {

// P(..., y, ...) from P(..., x, ...), x at position k, by P's congruence there.
H cong_atom(Tac& t, Lemmas& lm, H h, size_t k, const std::string& y, H exy) {
    FmP a = t.p.fm(h);
    const std::vector<std::string>& A = a->args;
    const std::string x = A[k];
    const std::string& p = a->name;
    auto use = [&](const std::string& n, const std::vector<std::string>& args, const std::vector<H>& ants) {
        return t.mp(t.inst(t.p.use(n), args), ants);
    };
    if (p == "elem") return k == 0 ? use("elem_first_subst", {x, y, A[1]}, {exy, h}) : use("elem_second", {x, y, A[0]}, {exy, h});
    if (p == "eq") return k == 0 ? use("eq_trans", {y, x, A[1]}, {t.p.eq_sym(exy), h}) : use("eq_trans", {A[0], x, y}, {h, exy});
    if (p == "zero") return use(lm.num_cong(0), {x, y}, {exy, h});
    if (p == "Sys.natural") return use(lm.nat_cong(), {x, y}, {exy, h});
    if (p == "tuple") return k == 0 ? use(lm.tuple_cong1(), {x, y, A[1]}, {exy, h}) : use(lm.tuple_cong2(), {A[0], x, y}, {exy, h});
    if (p == "pmem") {
        if (k == 0) return use(lm.pmem_cong1(), {x, y, A[1], A[2]}, {exy, h});
        if (k == 1) return use(lm.pmem_cong2(), {A[0], x, y, A[2]}, {exy, h});
        return use(lm.pmem_cong3(), {A[0], A[1], x, y}, {exy, h});
    }
    if (p == "nsucc") return k == 0 ? use("nsucc_CONG", {x, y, A[1]}, {exy, h}) : use(lm.nsucc_cong2(), {A[0], x, y}, {exy, h});
    if (p == "kpair") {
        if (k == 2) return use("kpair_res_cong", {A[0], A[1], x, y}, {h, exy});
        return use("kpair_arg_cong", {A[0], A[1], k == 0 ? y : A[0], k == 1 ? y : A[1], A[2]},
                   {h, k == 0 ? exy : refl(t, A[0]), k == 1 ? exy : refl(t, A[1])});
    }
    if (p == "snoc") {
        if (k == 3) return use("snoc_res_cong", {A[0], A[1], A[2], x, y}, {h, exy});
        std::vector<std::string> args;
        std::vector<H> ants;
        for (size_t j = 0; j < 3; ++j) {
            args.insert(args.end(), {A[j], j == k ? y : A[j]});
            ants.push_back(j == k ? exy : refl(t, A[j]));
        }
        args.push_back(A[3]);
        ants.push_back(h);
        return use("snoc_CONG", args, ants);
    }
    throw std::runtime_error("no congruence for " + p);
}

}  // namespace

H transport(Tac& t, Lemmas& lm, const std::string& x, const std::string& y, H exy, H h) {
    FmP f = t.p.fm(h);
    if (!free_vars(f).count(x)) return h;
    auto moved = [&](const FmP& g) { return subst(g, {{x, y}}); };
    auto back = [&](H g) { return transport(t, lm, y, x, t.p.eq_sym(exy), g); };
    auto on = [&](H g) { return transport(t, lm, x, y, exy, g); };
    switch (f->k) {
        case Fm::Atom:
            for (size_t k = 0; k < f->args.size(); ++k)
                if (t.p.fm(h)->args[k] == x) h = cong_atom(t, lm, h, k, y, exy);
            return h;
        case Fm::Not: return t.refute(moved(f->a), [&](H a) { return t.p.not_elim(h, back(a)); });
        case Fm::And: return t.p.and_intro(on(t.p.and_l(h)), on(t.p.and_r(h)));
        case Fm::Or:
            return t.cases(h, [&](H l) { return t.p.or_intro_l(on(l), moved(f->b)); },
                           [&](H r) { return t.p.or_intro_r(moved(f->a), on(r)); });
        case Fm::Imp: return t.assume(moved(f->a), [&](H a) { return on(t.p.implies_elim(h, back(a))); });
        case Fm::Iff: {
            H l = t.assume(moved(f->a), [&](H a) { return on(t.p.iff_l(h, back(a))); });
            H r = t.assume(moved(f->b), [&](H b) { return on(t.p.iff_r(h, back(b))); });
            return t.p.iff_intro(l, r);
        }
        case Fm::Forall:
            if (f->a->k != Fm::Imp || !(f->a->a->k == Fm::Atom && f->a->a->name == "set")) break;
            return t.all(f->name, [&](const std::string& w) { return on(t.inst(h, {w})); });
        case Fm::Exists:
            return t.obtain(h, f->name, [&](const std::string& w, H b) { return t.witness(moved(f), w, on(b)); });
        case Fm::False: return h;
    }
    throw std::runtime_error("transport through an unguarded quantifier: " + print(f).substr(0, 200));
}

}  // namespace sys2fol::prove
