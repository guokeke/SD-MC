
package org.xidian.dz.GUI;

import java.awt.Color;
import java.awt.Dimension;
import java.awt.Toolkit;
import java.awt.event.ActionEvent;
import java.awt.event.ActionListener;
import java.io.BufferedWriter;
import java.io.FileWriter;
import java.io.IOException;
import java.util.Arrays;
import java.util.Map;

import javax.swing.JButton;
import javax.swing.JComboBox;
import javax.swing.JFrame;
import javax.swing.JLabel;
import javax.swing.JOptionPane;

import org.sosy_lab.common.Pair;



public class PropertyGUI extends JFrame{

  private static final long serialVersionUID = 1L;
  /**
   * @param args
   */
  private JAutoCompleteComboBox combo;
  private String s;
  public static boolean f=true;
  private Map<String,Pair<String,String>> map;
  public PropertyGUI(Map<String,Pair<String,String>> pmap,String problem){
    setLayout(null);
    map=pmap;
    JLabel text=new JLabel(problem);
    text.setVisible(true);
    text.setLocation(10, 20);
    text.setSize(320,20);
    add(text);
    combo=new JAutoCompleteComboBox();
    combo.setEnabled(true);
    combo.setLocation(10,50);
    //combo.s
    combo.setSelectedIndex(-1);
    combo.setSize(320,20);
    //combo.addItem("请选择变量");
    //combo.setEditable(true);
    //combo.addItem("");
    Object[] array= map.keySet().toArray();
    Arrays.sort(array);
    int len=0;
    while(len<array.length){
      Pair<String,String> pair=map.get(array[len].toString());
      combo.addItem(array[len].toString());
      len++;
    }
    add(combo);
    //combo.setBackground(Color.gray);
    combo.setForeground(Color.black);
    combo.addActionListener(new ActionListener(){
      @Override
      public void actionPerformed(ActionEvent event) {
        s=((JComboBox<?>) event.getSource()).getSelectedItem().toString();
      }
    });

    combo.setMaximumRowCount(5);
    JButton ensure=new JButton("确定");
    ensure.setEnabled(true);
    ensure.setVisible(true);
    ensure.setLocation(80,80);
    ensure.setSize(80, 20);
    add(ensure);
    ensure.addActionListener(new ActionListener(){

      @Override
      public void actionPerformed(ActionEvent pE) {
        // TODO Auto-generated method stub
        if(!map.keySet().contains(s)){
          JOptionPane.showMessageDialog(null,
              "你选的指针变量不存在,请重新选择","Message：",
              JOptionPane.ERROR_MESSAGE);
        }
        else{
          s=map.get(s).getFirst()+"&&"+map.get(s).getSecond();
        FileWriter fr;
        try {
          fr = new FileWriter("D:\\property\\propositions.txt");
          BufferedWriter bufferWriter=new BufferedWriter(fr);
          bufferWriter.write(s);
          bufferWriter.flush();
          bufferWriter.close();
        } catch (IOException e) {
          // TODO Auto-generated catch block
          e.printStackTrace();
        }
        f=false;
        }
        //System.exit(1);
      }
    });
    JButton cancel=new JButton("退出");
    cancel.setEnabled(true);
    cancel.setVisible(true);
    cancel.setLocation(180,80);
    cancel.setSize(80, 20);
    add(cancel);
    cancel.addActionListener(new ActionListener(){

      @Override
      public void actionPerformed(ActionEvent pE) {
        // TODO Auto-generated method stub
        //s="";
        System.exit(0);
      }
    });
  }
  public void choose(){
    Dimension screenSize = Toolkit.getDefaultToolkit().getScreenSize();
    int x = (screenSize.width-this.getWidth())/2;
    int y = (screenSize.height-this.getHeight())/2;
    setLocation(x,y);
    setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
    setVisible(true);
    while(PropertyGUI.f);
    setEnabled(false);
    setVisible(false);
    dispose();
  }
 /* public static void main(String[] args) throws Throwable {
    // TODO Auto-generated method stub
    Map<String,Pair<String,String>> map=new HashMap<>();
    map.put("1", Pair.of("p=>x=1","q=>y=2"));
    map.put("2", Pair.of("p=>x=3","q=>y=2"));
    map.put("3", Pair.of("p=>x=4","q=>y=2"));
    PropertyGUI pg=new PropertyGUI(map);
    pg.setSize(300, 500);
    Dimension screenSize = Toolkit.getDefaultToolkit().getScreenSize();
    int x = (screenSize.width-pg.getWidth())/2;
    int y = (screenSize.height-pg.getHeight())/2;
    pg.setLocation(x,y);
    pg.setDefaultCloseOperation(EXIT_ON_CLOSE);
    pg.setVisible(true);
    while(f);
    System.out.println("ok");
  }*/

}
