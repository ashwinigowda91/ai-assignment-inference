
import java.util.*;
import java.io.*;

public class BC {
    
public static String tell;
public static String ask;
public static ArrayList<String> agenda;
public static ArrayList<String> facts;
public static ArrayList<String> clauses;
public static ArrayList<String> entailed;
public static ArrayList<String> actors;
 
public BC(String a, String t){
	
	agenda  = new ArrayList<String>();
	clauses  = new ArrayList<String>();
	entailed  = new ArrayList<String>();
	facts  = new ArrayList<String>();
        actors = new ArrayList<String>();
	tell = t;
	ask = a;
        
	init(tell);
        agenda.add(ask);
        refreshAgenda(ask);
        
        for(String ec : clauses)
        {
            ArrayList<String> premises = getPremises(ec);
            for(String var : premises){
                refreshAgenda(ec);
            }
            
            refreshAgenda(getRightSide(ec));
        }
        
        for(String ec : facts)
        {
            refreshAgenda(ec);
        }
        
        for(String ea:actors)
        {
            replaceX(ea);
        }
        
        removeX();
}
 
public void removeX()
{
        for (int i = 0; i < clauses.size(); i++) {
        
            if (clauses.get(i).contains("x")) {
                clauses.remove(i);
            }
        }
        
        for (int j = 0; j < facts.size(); j++) {
        
            if (facts.get(j).contains("x")) {
                facts.remove(j);
            }
        }
}
public void replaceX(String value)
{
    ArrayList<String> tempStrings = new ArrayList<String>();
    for(String eachClause : clauses)
    {
        String temp = eachClause;
        temp = temp.replaceAll("x", value);
        tempStrings.add(temp);
    }
    
     for(String eachTemp:tempStrings)
    {
        if(!clauses.contains(eachTemp)){
            clauses.add(eachTemp);
        }
    }
    
     tempStrings = new ArrayList<String>();
     
    for(String eachFact : facts)
    {
        String temp = eachFact;
        temp = temp.replaceAll("x", value);
        tempStrings.add(temp);
    }
    
    for(String eachTemp:tempStrings)
    {
        if(!facts.contains(eachTemp)){
            facts.add(eachTemp);
        }
    }
    
}
public  void refreshAgenda(String premise){
        
    String value = ""; 
    
    if (premise.equalsIgnoreCase("null")) {
        return;
    }
    
    if(premise.contains(","))
    {
    int breakPoint1=premise.indexOf("(");
    int breakPoint2=premise.indexOf(")");
    String subString = premise.substring(breakPoint1+1, breakPoint2);
    String[] splitStrings = subString.split(",");
    
    for ( String boo : splitStrings)
    {
        if (!actors.contains(boo)) {
            actors.add(boo);
        }
    }
    }
    else
    {
            int breakPoint1=premise.indexOf("(");
            int breakPoint2=premise.indexOf(")");
            value=premise.substring(breakPoint1+1,breakPoint2);
            
            if (!actors.contains(value)) {
            actors.add(value);
        }
    }
}
 

public static void init(String tell){
	
        

   String[] sentences = tell.split(";");
	for (int i=0;i<sentences.length;i++){
		if (!sentences[i].contains("=>")) 
			
			facts.add(sentences[i]);
		else{
			
			clauses.add(sentences[i]);
			}
	}
}
 

public String execute(){
	String output = "";
 
	if (checkIfThisIsTrue(ask)){
		
		output = "TRUE";
			}
	// no 
	else{
			output = "FALSE";
	}
	return output;		
}




public boolean checkIfThisIsTrue(String sense)
{
    
    if (facts.contains(sense)) {
        return true;
    }
    
    for(String eachClause : clauses)
    {
        if(conclusionContains(eachClause, sense))
        {
            boolean flag =true;
            ArrayList<String> temp = getPremises(eachClause);
            
            for(String eachPremise : temp)
            {
               flag = flag && checkIfThisIsTrue(eachPremise);
            }
            
            if (flag) {
                return true;
            }
        }
    }
    
    return false;
}


public static ArrayList<String> getPremises(String clause){
	String premise = clause.split("=>")[0];
	ArrayList<String> temp = new ArrayList<String>();
	String[] conjuncts = premise.split("&");
	
	for(int i=0;i<conjuncts.length;i++){
			if (!agenda.contains(conjuncts[i]))
					temp.add(conjuncts[i]);
	}
	
	return temp;
}
 
 

public static boolean conclusionContains(String clause, String c){
	String conclusion = clause.split("=>")[1];
	if (conclusion.equals(c))
		return true;
	else
		return false;
 
}

public static String getRightSide(String clause)
{
    String conclusion = clause.split("=>")[1];
    return conclusion;
}

}
