import java.util.ArrayList;
import java.util.List;


public class test {

	/**
	 * @param args
	 */
	public static void main(String[] args) {
		
		String str = "D(x,y) ^ Q(y)";
		String[] split = str.split("\\^");
		for(int k=0; k<split.length; k++)
		{
			System.out.println(split[k].trim());
		}
	}

}
