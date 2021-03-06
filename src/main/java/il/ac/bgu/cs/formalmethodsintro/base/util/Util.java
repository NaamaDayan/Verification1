package il.ac.bgu.cs.formalmethodsintro.base.util;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import il.ac.bgu.cs.formalmethodsintro.base.automata.Automaton;
import il.ac.bgu.cs.formalmethodsintro.base.automata.MultiColorAutomaton;
import il.ac.bgu.cs.formalmethodsintro.base.ltl.LTL;

/**
 * Utility methods for implementation.
 */
public class Util {

    public static <T1, T2> Set<Pair<T1, T2>> getPairs(Set<T1> s1, Set<T2> s2) {
        Stream<Pair<T1, T2>> str = s1.stream().flatMap(e1 -> s2.stream().map(e2 -> new Pair<>(e1, e2))); //
        return str.collect(Collectors.toSet());
    }

    public static <T> Set<Set<T>> powerSet(Set<T> aset) {
        List<T> orderedItems = new ArrayList<>(aset);
        IntStream powerSetMemberIdxs = IntStream.range(0, (int) Math.pow(2, aset.size()));

        Stream<Set<T>> stream = powerSetMemberIdxs.parallel().mapToObj(e -> {
            IntStream range2 = IntStream.range(0, orderedItems.size());
            return range2.filter(i -> (e & (0b1 << i)) != 0).mapToObj(i -> orderedItems.get(i)).collect(Collectors.toSet());
        });

        return stream.collect(Collectors.toSet());
    }

    /**
     * @param gnba
     */
    public static <L> void printColoredAutomatonTransitions(MultiColorAutomaton<Set<LTL<L>>, L> gnba) {
        gnba.getTransitions().entrySet().stream()
                .forEach((s1) -> s1.getValue().entrySet().stream().forEach(s2 -> s2.getValue().stream()
                .forEach(s3 -> System.out.println(s1.getKey() + "----" + s2.getKey() + "---->" + s3))));
    }

    /**
//     * @param gnba
     */
    public static <S, L> void printAutomatonTransitions(Automaton<S, L> nba) {
        nba.getTransitions().entrySet().stream()
                .forEach((s1) -> s1.getValue().entrySet().stream().forEach(s2 -> s2.getValue().stream()
                .forEach(s3 -> System.out.println(s1.getKey() + "----" + s2.getKey() + "---->" + s3))));
    }

    public static <S> List<Set<S>> cartesianProduct(List<Set<S>> sets) {
        if (sets.size() < 2)
            return sets;

        return _cartesianProduct(0, sets);
    }
    public static <S> int indexOfElement (List<S> lst, S element){
        int i = 0 ;
        for(S ele: lst) {
            if (ele.equals(element))
                return i;
            i += 1;
        }
        return -1;
    }
    public static boolean isNumber(String num) {
        try {
            int x = Integer.parseInt(num);
            return true;
        } catch (Exception e) {
            return false;
        }
    }

    private static <S> List<Set<S>> _cartesianProduct(int index, List<Set<S>> sets) {
        List<Set<S>> ret = new LinkedList<Set<S>>();
        if (index == sets.size()) {
            ret.add(new HashSet<S>());
        } else {
            for (S obj : sets.get(index)) {
                for (Set<S> set : _cartesianProduct(index+1, sets)) {
                    set.add(obj);
                    ret.add(set);
                }
            }
        }
        return ret;
    }

    public static <L> Pair<List<L>, Map<String, Object>> stateCopy(Pair<List<L>, Map<String, Object>> state){
        List<L> copyL = new LinkedList<>(state.getFirst());
        Map<String, Object> copyM = new HashMap<>(state.getSecond());
        return new Pair<List<L>, Map<String, Object>>(copyL, copyM);
    }

    public static Map<String, Object> deepCopyM(Map<String, Object> toCopy){
        Map<String,Object> toRet = new HashMap<>();
        for (Map.Entry etry : toCopy.entrySet())
            if (etry.getValue() instanceof Queue)
                toRet.put((String)etry.getKey(), new LinkedList((Queue)etry.getValue()));
            else
                toRet.put((String) etry.getKey(), etry.getValue());
            return toRet;
    }

}


