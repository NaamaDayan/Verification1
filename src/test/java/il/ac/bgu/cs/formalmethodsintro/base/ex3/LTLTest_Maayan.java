package il.ac.bgu.cs.formalmethodsintro.base.ex3;

import static il.ac.bgu.cs.formalmethodsintro.base.ltl.LTL.*;
import static il.ac.bgu.cs.formalmethodsintro.base.util.CollectionHelper.set;
import static org.junit.Assert.assertEquals;

import java.util.HashSet;
import java.util.Set;

import org.junit.Test;

import il.ac.bgu.cs.formalmethodsintro.base.FvmFacade;
import il.ac.bgu.cs.formalmethodsintro.base.automata.Automaton;
import il.ac.bgu.cs.formalmethodsintro.base.ltl.AP;
import il.ac.bgu.cs.formalmethodsintro.base.ltl.LTL;
import il.ac.bgu.cs.formalmethodsintro.base.ltl.Not;
import il.ac.bgu.cs.formalmethodsintro.base.ltl.TRUE;
import il.ac.bgu.cs.formalmethodsintro.base.ltl.Until;
import il.ac.bgu.cs.formalmethodsintro.base.util.Pair;

public class LTLTest_Maayan {

    FvmFacade fvmFacadeImpl = FvmFacade.get();

    @Test
    public void test2() {
        AP<String> a = new AP<>("a");
        AP<String> b = new AP<>("b");
        LTL<String> ltl = until(a,b);

        Automaton<?, String> aut = fvmFacadeImpl.LTL2NBA(ltl);
        Automaton<?, String> exp = expected2();


        assertEquals(aut.equals(exp), true);

    }

    Automaton<Pair<Set<String>, Integer>, String> expected() {
        Automaton<Pair<Set<String>, Integer>, String> aut = new Automaton<>();

        Pair<Set<String>, Integer> p_np = new Pair<>(set("!(!p /\\ ()p)", "()p", "p"), 0);
        Pair<Set<String>, Integer> p_notnp = new Pair<>(set("!(!p /\\ ()p)", "!()p", "p"), 0);
        Pair<Set<String>, Integer> notp_np = new Pair<>(set("(!p /\\ ()p)", "!p", "()p"), 0);
        Pair<Set<String>, Integer> notp_notnp = new Pair<>(set("!(!p /\\ ()p)", "!()p", "!p"), 0);

        Set<String> p = set("p");
        Set<String> notp = set();

        aut.addTransition(notp_notnp, notp, notp_np);
        aut.addTransition(notp_notnp, notp, notp_notnp);
        aut.addTransition(p_notnp, p, notp_notnp);
        aut.addTransition(p_notnp, p, notp_np);
        aut.addTransition(notp_np, notp, p_np);
        aut.addTransition(notp_np, notp, p_notnp);
        aut.addTransition(p_np, p, p_np);
        aut.addTransition(p_np, p, p_notnp);

        aut.setInitial(notp_np);

        aut.setAccepting(p_np);
        aut.setAccepting(p_notnp);
        aut.setAccepting(notp_np);
        aut.setAccepting(notp_notnp);

        return aut;

    }

    Automaton<Pair<Set<LTL<String>>,Integer>, String> expected2() {
        Automaton<Pair<Set<LTL<String>>,Integer>, String> aut = new Automaton<>();

        Set<LTL<String>> s1 = new HashSet<>();
        s1.add(new AP<String>("a"));
        s1.add(new  AP<String>("b"));
        s1.add(new Until<String>(new AP<String>("a"), new  AP<String>("b")));

        Set<LTL<String>> s2 = new HashSet<>();
        s2.add(new AP<String>("a"));
        s2.add(new Not<String>(new  AP<String>("b")));
        s2.add(new Until<String>(new AP<String>("a"), new  AP<String>("b")));

        Set<LTL<String>> s3 = new HashSet<>();
        s3.add(new Not<String>(new AP<String>("a")));
        s3.add(new AP<String>("b"));
        s3.add(new Until<String>(new AP<String>("a"), new  AP<String>("b")));

        Set<LTL<String>> s4 = new HashSet<>();
        s4.add(new AP<String>("a"));
        s4.add(new Not<String>(new AP<String>("b")));
        s4.add(new Not<String>(new Until<String>(new AP<String>("a"), new  AP<String>("b"))));

        Set<LTL<String>> s5 = new HashSet<>();
        s5.add(new Not<String>(new AP<String>("a")));
        s5.add(new Not<String>(new AP<String>("b")));
        s5.add(new Not<String>(new Until<String>(new AP<String>("a"), new  AP<String>("b"))));


        Set<String> a = set("a");
        Set<String> b = set("b");
        Set<String> ab = set("a","b");
        Set<String> not = set();

        aut.setInitial(Pair.pair(s1,0));
        aut.setInitial(Pair.pair(s2,0));
        aut.setInitial(Pair.pair(s3,0));

        aut.setAccepting(Pair.pair(s1,0));
        aut.setAccepting(Pair.pair(s3,0));
        aut.setAccepting(Pair.pair(s4,0));
        aut.setAccepting(Pair.pair(s5,0));

        aut.addTransition(Pair.pair(s1,0),ab,Pair.pair(s1,0));
        aut.addTransition(Pair.pair(s1,0),ab,Pair.pair(s2,0));
        aut.addTransition(Pair.pair(s1,0),ab,Pair.pair(s3,0));
        aut.addTransition(Pair.pair(s1,0),ab,Pair.pair(s4,0));
        aut.addTransition(Pair.pair(s1,0),ab,Pair.pair(s5,0));

        aut.addTransition(Pair.pair(s2,0),a,Pair.pair(s2,0));
        aut.addTransition(Pair.pair(s2,0),a,Pair.pair(s1,0));
        aut.addTransition(Pair.pair(s2,0),a,Pair.pair(s3,0));

        aut.addTransition(Pair.pair(s3,0),b,Pair.pair(s3,0));
        aut.addTransition(Pair.pair(s3,0),b,Pair.pair(s1,0));
        aut.addTransition(Pair.pair(s3,0),b,Pair.pair(s2,0));
        aut.addTransition(Pair.pair(s3,0),b,Pair.pair(s4,0));
        aut.addTransition(Pair.pair(s3,0),b,Pair.pair(s5,0));

        aut.addTransition(Pair.pair(s4,0),a,Pair.pair(s4,0));
        aut.addTransition(Pair.pair(s4,0),a,Pair.pair(s5,0));

        aut.addTransition(Pair.pair(s5,0),not,Pair.pair(s5,0));
        aut.addTransition(Pair.pair(s5,0),not,Pair.pair(s1,0));
        aut.addTransition(Pair.pair(s5,0),not,Pair.pair(s2,0));
        aut.addTransition(Pair.pair(s5,0),not,Pair.pair(s3,0));
        aut.addTransition(Pair.pair(s5,0),not,Pair.pair(s4,0));


        return aut;

    }

    @Test
    public void test3() {
        AP<String> a = new AP<>("a");
        AP<String> b = new AP<>("b");
        LTL<String> ltlInner = until(a,b);
        LTL<String> ltlOuter = until(new TRUE<String>(),new Not<String>(ltlInner));

        Automaton<?, String> aut = fvmFacadeImpl.LTL2NBA(ltlOuter);

        assertEquals(aut.equals(expected3()), true);
    }

    Automaton<Pair<Set<LTL<String>>,Integer>, String> expected3() {
        Automaton<Pair<Set<LTL<String>>,Integer>, String> aut = new Automaton<>();
        AP<String> a = new AP<>("a");
        AP<String> b = new AP<>("b");
        LTL<String> ltlInner = until(new AP<>("a"), new AP<>("b"));
        LTL<String> ltlOuter = until(new TRUE<String>(),new Not<String>(ltlInner));

        Set<LTL<String>> s1 = new HashSet<>();
        s1.add(new AP<>("a"));
        s1.add(until(new TRUE<String>(),new Not<String>(until(new AP<>("a"), new AP<>("b")))));
        s1.add(new Not<String>(new AP<>("b")));
        s1.add(new Not<String>(until(new AP<>("a"), new AP<>("b"))));
        s1.add(new TRUE<String>());

        Set<LTL<String>> s2 = new HashSet<>();
        s2.add(until(new TRUE<String>(),new Not<String>(until(new AP<>("a"), new AP<>("b")))));
        s2.add(new AP<>("a"));
        s2.add(until(new AP<>("a"), new AP<>("b")));
        s2.add(new Not<String>(new AP<>("b")));
        s2.add(new TRUE<String>());

        Set<LTL<String>> s3 = new HashSet<>();
        s3.add(until(new TRUE<String>(),new Not<String>(until(new AP<>("a"), new AP<>("b")))));
        s3.add(new AP<>("a"));
        s3.add(new AP<>("b"));
        s3.add(until(new AP<>("a"), new AP<>("b")));
        s3.add(new TRUE<String>());

        Set<LTL<String>> s4 = new HashSet<>();
        s4.add(until(new TRUE<String>(),new Not<String>(until(new AP<>("a"), new AP<>("b")))));
        s4.add(new AP<>("b"));
        s4.add(until(new AP<>("a"), new AP<>("b")));
        s4.add(new Not<String>(new AP<>("a")));
        s4.add(new TRUE<String>());

        Set<LTL<String>> s5 = new HashSet<>();
        s5.add(until(new TRUE<String>(),new Not<String>(until(new AP<>("a"), new AP<>("b")))));
        s5.add(new Not<String>(new AP<>("a")));
        s5.add(new Not<String>(new AP<>("b")));
        s5.add(new Not<String>(until(new AP<>("a"), new AP<>("b"))));
        s5.add(new TRUE<String>());

        Set<LTL<String>> s6 = new HashSet<>();
        s6.add(new AP<>("b"));
        s6.add(until(new AP<>("a"), new AP<>("b")));
        s6.add(new Not<String>(new AP<>("a")));
        s6.add(new Not<String> (until(new TRUE<String>(),new Not<String>(until(new AP<>("a"), new AP<>("b"))))));
        s6.add(new TRUE<String>());

        Set<LTL<String>> s7 = new HashSet<>();
        s7.add(new AP<>("a"));
        s7.add(new AP<>("b"));
        s7.add(until(new AP<>("a"), new AP<>("b")));
        s7.add(new Not<String> (until(new TRUE<String>(),new Not<String>(until(new AP<>("a"), new AP<>("b"))))));
        s7.add(new TRUE<String>());

        Set<LTL<String>> s8 = new HashSet<>();
        s8.add(new AP<>("a"));
        s8.add(until(new AP<>("a"), new AP<>("b")));
        s8.add(new Not<String> (until(new TRUE<String>(),new Not<String>(until(new AP<>("a"), new AP<>("b"))))));
        s8.add(new Not<String>(new AP<>("b")));
        s8.add(new TRUE<String>());

        aut.setInitial(Pair.pair(s1, 0));
        aut.setInitial(Pair.pair(s2, 0));
        aut.setInitial(Pair.pair(s3, 0));
        aut.setInitial(Pair.pair(s4, 0));
        aut.setInitial(Pair.pair(s5, 0));

        aut.setAccepting(Pair.pair(s1, 0));
        aut.setAccepting(Pair.pair(s3, 0));
        aut.setAccepting(Pair.pair(s4, 0));
        aut.setAccepting(Pair.pair(s5, 0));
        aut.setAccepting(Pair.pair(s6, 0));
        aut.setAccepting(Pair.pair(s7, 0));

        Set<String> a_set = set("a");
        Set<String> b_set = set("b");
        Set<String> ab_set = set("a","b");
        Set<String> not_set = set();

        aut.addTransition(Pair.pair(s1, 0),a_set ,Pair.pair(s1, 1) );
        aut.addTransition(Pair.pair(s1, 0),a_set ,Pair.pair(s5, 1) );

        aut.addTransition(Pair.pair(s2,0), a_set, Pair.pair(s2, 0));
        aut.addTransition(Pair.pair(s2,0), a_set, Pair.pair(s3, 0));
        aut.addTransition(Pair.pair(s2,0), a_set, Pair.pair(s4, 0));

        aut.addTransition(Pair.pair(s3, 0), ab_set, Pair.pair(s1, 1));
        aut.addTransition(Pair.pair(s3, 0), ab_set, Pair.pair(s2, 1));
        aut.addTransition(Pair.pair(s3, 0), ab_set, Pair.pair(s3, 1));
        aut.addTransition(Pair.pair(s3, 0), ab_set, Pair.pair(s4, 1));
        aut.addTransition(Pair.pair(s3, 0), ab_set, Pair.pair(s5, 1));

        aut.addTransition(Pair.pair(s4, 0), b_set, Pair.pair(s1, 1));
        aut.addTransition(Pair.pair(s4, 0), b_set, Pair.pair(s2, 1));
        aut.addTransition(Pair.pair(s4, 0), b_set, Pair.pair(s3, 1));
        aut.addTransition(Pair.pair(s4, 0), b_set, Pair.pair(s4, 1));
        aut.addTransition(Pair.pair(s4, 0), b_set, Pair.pair(s5, 1));

        aut.addTransition(Pair.pair(s5, 0), not_set, Pair.pair(s1, 1));
        aut.addTransition(Pair.pair(s5, 0), not_set, Pair.pair(s2, 1));
        aut.addTransition(Pair.pair(s5, 0), not_set, Pair.pair(s3, 1));
        aut.addTransition(Pair.pair(s5, 0), not_set, Pair.pair(s4, 1));
        aut.addTransition(Pair.pair(s5, 0), not_set, Pair.pair(s5, 1));
        aut.addTransition(Pair.pair(s5, 0), not_set, Pair.pair(s6, 1));
        aut.addTransition(Pair.pair(s5, 0), not_set, Pair.pair(s7, 1));
        aut.addTransition(Pair.pair(s5, 0), not_set, Pair.pair(s8, 1));

        aut.addTransition(Pair.pair(s6, 0), b_set, Pair.pair(s6, 1));
        aut.addTransition(Pair.pair(s6, 0), b_set, Pair.pair(s7, 1));
        aut.addTransition(Pair.pair(s6, 0), b_set, Pair.pair(s8, 1));

        aut.addTransition(Pair.pair(s7, 0), ab_set, Pair.pair(s6, 1));
        aut.addTransition(Pair.pair(s7, 0), ab_set, Pair.pair(s7, 1));
        aut.addTransition(Pair.pair(s7, 0), ab_set, Pair.pair(s8, 1));

        aut.addTransition(Pair.pair(s8, 0), a_set, Pair.pair(s6, 0));
        aut.addTransition(Pair.pair(s8, 0), a_set, Pair.pair(s7, 0));
        aut.addTransition(Pair.pair(s8, 0), a_set, Pair.pair(s8, 0));

        aut.addTransition(Pair.pair(s1, 1), a_set, Pair.pair(s1, 0));
        aut.addTransition(Pair.pair(s1, 1), a_set, Pair.pair(s5, 0));

        aut.addTransition(Pair.pair(s2, 1), a_set, Pair.pair(s2,1));
        aut.addTransition(Pair.pair(s2, 1), a_set, Pair.pair(s3,1));
        aut.addTransition(Pair.pair(s2, 1), a_set, Pair.pair(s4,1));

        aut.addTransition(Pair.pair(s3, 1), ab_set, Pair.pair(s1, 1));
        aut.addTransition(Pair.pair(s3, 1), ab_set, Pair.pair(s2, 1));
        aut.addTransition(Pair.pair(s3, 1), ab_set, Pair.pair(s3, 1));
        aut.addTransition(Pair.pair(s3, 1), ab_set, Pair.pair(s4, 1));
        aut.addTransition(Pair.pair(s3, 1), ab_set, Pair.pair(s5, 1));

        aut.addTransition(Pair.pair(s4, 1), b_set, Pair.pair(s1, 1));
        aut.addTransition(Pair.pair(s4, 1), b_set, Pair.pair(s2, 1));
        aut.addTransition(Pair.pair(s4, 1), b_set, Pair.pair(s3, 1));
        aut.addTransition(Pair.pair(s4, 1), b_set, Pair.pair(s4, 1));
        aut.addTransition(Pair.pair(s4, 1), b_set, Pair.pair(s5, 1));

        aut.addTransition(Pair.pair(s5, 1), not_set, Pair.pair(s1, 0));
        aut.addTransition(Pair.pair(s5, 1), not_set, Pair.pair(s2, 0));
        aut.addTransition(Pair.pair(s5, 1), not_set, Pair.pair(s3, 0));
        aut.addTransition(Pair.pair(s5, 1), not_set, Pair.pair(s4, 0));
        aut.addTransition(Pair.pair(s5, 1), not_set, Pair.pair(s5, 0));
        aut.addTransition(Pair.pair(s5, 1), not_set, Pair.pair(s6, 0));
        aut.addTransition(Pair.pair(s5, 1), not_set, Pair.pair(s7, 0));
        aut.addTransition(Pair.pair(s5, 1), not_set, Pair.pair(s8, 0));


        aut.addTransition(Pair.pair(s6, 1), b_set, Pair.pair(s6, 0));
        aut.addTransition(Pair.pair(s6, 1), b_set, Pair.pair(s7, 0));
        aut.addTransition(Pair.pair(s6, 1), b_set, Pair.pair(s8, 0));

        aut.addTransition(Pair.pair(s7, 1), ab_set, Pair.pair(s6, 0));
        aut.addTransition(Pair.pair(s7, 1), ab_set, Pair.pair(s7, 0));
        aut.addTransition(Pair.pair(s7, 1), ab_set, Pair.pair(s8, 0));

        aut.addTransition(Pair.pair(s8, 1), a_set, Pair.pair(s6, 0));
        aut.addTransition(Pair.pair(s8, 1), a_set, Pair.pair(s7, 0));
        aut.addTransition(Pair.pair(s8, 1), a_set, Pair.pair(s8, 0));


        return aut;
    }


}
