package il.ac.bgu.cs.formalmethodsintro.base.programgraph;

import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Queue;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;

import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.Evaluator;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaLexer;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaParser;
import il.ac.bgu.cs.formalmethodsintro.base.nanopromela.NanoPromelaParser.BoolexprContext;

/**
 * An object that identifies and interprets the conditions defined in the
 * grammar nanopromela/NanoPromela.g4
 */
public class ParserBasedCondDef implements ConditionDef {

    /**
     * @see il.ac.bgu.cs.formalmethodsintro.base.programgraph.ConditionDef#evaluate(java.util.Map,
     * java.lang.String)
     */
    @Override
    public boolean evaluate(Map<String, Object> eval, String condition) {
        if (condition.equals("")) {
            return true;
        }

        if (! isLegallChannelCond(eval, condition))
            return false;

        condition = removeChannelFromCond(condition);
        if (condition.equals(""))
            return true;

        NanoPromelaLexer lexer = new NanoPromelaLexer(new ANTLRInputStream(condition));
        CommonTokenStream tokens = new CommonTokenStream(lexer);
        NanoPromelaParser parser = new NanoPromelaParser(tokens);

        lexer.removeErrorListeners();
        lexer.addErrorListener(new ThrowingErrorListener());

        parser.removeErrorListeners();
        parser.addErrorListener(new ThrowingErrorListener());

        BoolexprContext context = parser.boolexpr();

        return new Evaluator(eval).evaluate(context);
    }

    private String removeChannelFromCond(String condition) {
        if (condition.contains("size")) {
            condition = condition.replaceAll("\\s+", ""); //remove all whitespaces3
            int startChannel = condition.indexOf("size");
            if (startChannel > 3 && (condition.charAt(startChannel-1)=='&' ||condition.charAt(startChannel-1)=='|'))
                startChannel -=2;
            condition = condition.substring(0, startChannel);
        }
        return condition;
    }

    private boolean isLegallChannelCond(Map<String, Object> eval, String condition) {
        if (condition.contains("size")) {
            int channelStartInd = condition.indexOf("size(") + 5; //+size(
            String channel = condition.substring(channelStartInd);
            int end = channel.length() > channel.indexOf(' ') ? channel.length() : channel.indexOf(' ');
            channel = channel.substring(0, end);
            boolean equall = channel.contains("=");
            boolean smaller = condition.contains("<");
            boolean larger = condition.contains(">");
            end = channel.length() > channel.indexOf(' ') ? channel.length() : channel.indexOf(' ');
            int value = Integer.parseInt(channel.substring(channel.indexOf(")") + 2, end));
            channel = channel.substring(0, channel.indexOf(")"));
            return (equall && (((Queue) (eval.get(channel))).size() == value)) || (larger && (((Queue) (eval.get(channel))).size() > value)) || (smaller && (((Queue) (eval.get(channel))).size() < value));
        }
        return true;
    }


}
