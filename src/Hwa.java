import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Scanner;

import javax.swing.text.StyledEditorKit.BoldAction;

public class Hwa {

   
    public static void main(String[] args) {
        
        
        BufferedReader br = null;
	String sCurrentLine;
	int count=0;
	String ask = null;
	String tell=null;
	String value = null;
	String file2;
	//System.out.println("Enter the name of the file");
	//Scanner scanner = new Scanner(System.in);
//file2 = scanner.nextLine();
	try {
	br = new BufferedReader(new FileReader("input.txt"));
		//br = new BufferedReader(new FileReader(file2));
		while ((sCurrentLine = br.readLine()) != null) 
		{
		count++;
		if(count==1)
		{
			ask= sCurrentLine;
			if(ask.contains(","))
			{
			int breakPoint1=ask.indexOf("(");
			int breakPoint2=ask.indexOf(",");
			value=ask.substring(breakPoint1+1, breakPoint2);
			}
			else
			{
				int breakPoint1=ask.indexOf("(");
				int breakPoint2=ask.indexOf(")");
				value=ask.substring(breakPoint1+1,breakPoint2);
			}
		}
		else if(count>=3)
		{
			/*if(sCurrentLine.contains("x"))
			{
				sCurrentLine=sCurrentLine.replaceAll("x", value);
			}*/
			tell+=";"+sCurrentLine;	
		}
			
		}
	} catch (Exception e) {
		
		e.printStackTrace();
	}
	
	BC bc=new BC(ask,tell);
	String output=bc.execute();
	File file = new File("output.txt");
	if (!file.exists()) {
		try {
			file.createNewFile();
		} catch (IOException e) {
			
			e.printStackTrace();
		}
	}
	FileWriter fw;
	try {
		fw = new FileWriter(file);
		BufferedWriter bw = new BufferedWriter(fw);
		bw.write(output+"\n");
		bw.flush();
		bw.close();
	} catch (Exception e) {
		
		e.printStackTrace();
	}
	


        
    }
    
}
