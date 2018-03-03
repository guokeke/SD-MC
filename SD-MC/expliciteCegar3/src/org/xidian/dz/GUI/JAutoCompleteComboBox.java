/*
 *  CPAchecker is a tool for configurable software verification.
 *  This file is part of CPAchecker.
 *
 *  Copyright (C) 2007-2014  Dirk Beyer
 *  All rights reserved.
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 *
 *
 *  CPAchecker web page:
 *    http://cpachecker.sosy-lab.org
 */
package org.xidian.dz.GUI;

import java.awt.event.ItemEvent;
import java.awt.event.ItemListener;
import java.awt.event.KeyEvent;
import java.awt.event.KeyListener;
import java.util.Arrays;
import java.util.List;
import java.util.Vector;

import javax.swing.ComboBoxModel;
import javax.swing.DefaultComboBoxModel;
import javax.swing.JComboBox;
import javax.swing.JFrame;
import javax.swing.JTextField;


public class JAutoCompleteComboBox extends JComboBox<Object> {

  private static final long serialVersionUID = 1L;

  private AutoCompleter completer;

  public JAutoCompleteComboBox() {
   super();
   addCompleter();
  }

  public JAutoCompleteComboBox(ComboBoxModel cm) {
   super(cm);
   addCompleter();
  }

  public JAutoCompleteComboBox(Object[] items) {
   super(items);
   addCompleter();
  }

  public JAutoCompleteComboBox(List v) {
   super((Vector) v);
   addCompleter();
  }

  private void addCompleter() {
   setEditable(true);
   completer = new AutoCompleter(this);
  }

  public void autoComplete(String str) {
   this.completer.autoComplete(str, str.length());
  }

  public String getText() {
   return ((JTextField) getEditor().getEditorComponent()).getText();
  }

  public void setText(String text) {
   ((JTextField) getEditor().getEditorComponent()).setText(text);
  }

  public boolean containsItem(String itemString) {
   for (int i = 0; i < this.getModel().getSize(); i++) {
    String _item = "" + this.getModel().getElementAt(i);
    if (_item.equals(itemString)) {
     return true;
    }
   }
   return false;
  }

  /*
   * 测试方法
   */
  public static void main(String[] args) {
   JFrame frame = new JFrame();
   Object[] items = new Object[] { "zzz", "zba", "aab", "abc", "aab",
     "dfg", "aba", "hpp", "pp", "hlp", "王正权", "杨立国", "张红雨", "刘秀华",
     "王正华", "倪丽丽", "杨玉环" };
   // 排""序内容
   // java.util.ArrayList list = new
   // java.util.ArrayList(Arrays.asList(items));
   // Collections.sort(list);
   // JComboBox cmb = new JAutoCompleteComboBox(list.toArray());
   Arrays.sort(items);
   JComboBox cmb = new JAutoCompleteComboBox(items);
   cmb.setSelectedIndex(-1);
   frame.getContentPane().add(cmb);
   frame.pack();
   frame.setVisible(true);
   frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);
  }
 }

 /**
  * 自动完成器。自动找到最匹配的项目，并排在列表的最前面。
  *
  * @author SamZheng
  */

 @SuppressWarnings("unchecked")
 class AutoCompleter implements KeyListener   , ItemListener  {

  private JComboBox owner = null;

  private JTextField editor = null;

  private ComboBoxModel model = null;

  public AutoCompleter(JComboBox comboBox) {
   owner = comboBox;
   editor = (JTextField) comboBox.getEditor().getEditorComponent();
   editor.addKeyListener(this);
   model = comboBox.getModel();
    owner.addItemListener(this);
  }

  @Override
  public void keyTyped(KeyEvent e) {
  }

  @Override
  public void keyPressed(KeyEvent e) {
  }

  @Override
  public void keyReleased(KeyEvent e) {

   char ch = e.getKeyChar();
   /*
    * if (ch == KeyEvent.CHAR_UNDEFINED || Character.isISOControl(ch)|| ch ==
    * KeyEvent.VK_DELETE) { System.out.println("key=="+ch); return; }
    */

   if (ch == KeyEvent.VK_ENTER) {
    System.out.println("select item=="+String.valueOf(owner.getSelectedItem()));
    System.out.println("select index=="+owner.getSelectedIndex());
    editor.setText(String.valueOf(owner.getSelectedItem()));
    return;
   }
   int caretPosition = editor.getCaretPosition();
   String str = editor.getText();
   if (str.length() == 0) {
    return;
   }
   autoComplete(str, caretPosition);
  }

  /**
   * 自动完成。根据输入的内容，在列表中找到相似的项目.
   */
  protected void autoComplete(String strf, int caretPosition) {
   Object[] opts;
   opts = getMatchingOptions(strf.substring(0, caretPosition));
   if (owner != null) {
    model = new DefaultComboBoxModel(opts);
    owner.setModel(model);
   }
   if (opts.length > 0) {
    // String str = opts[0].toString();
    //System.out.println("1:"+caretPosition+","+editor.getText().length());
    if (caretPosition > editor.getText().length())
     return;
    editor.setCaretPosition(caretPosition);
    editor.setText(editor.getText().trim().substring(0, caretPosition));
    if (owner != null) {
     try {
      owner.showPopup();
     } catch (Exception ex) {
      ex.printStackTrace();
     }
    }
   }
  }

  /**
   *
   * 找到相似的项目, 并且将之排列到数组的最前面。
   *
   * @param str
   * @return 返回所有项目的列表。
   */
  protected Object[] getMatchingOptions(String str) {
   List<Object> v = new Vector<Object>();
   List<Object> v1 = new Vector<Object>();

   for (int k = 0; k < model.getSize(); k++) {
    Object itemObj = model.getElementAt(k);
    if (itemObj != null) {
     String item = itemObj.toString().toLowerCase();
     if (item.startsWith(str.toLowerCase())) {
      v.add(model.getElementAt(k));
     } else {
      v1.add(model.getElementAt(k));
     }
    } else {
     v1.add(model.getElementAt(k));
    }
   }
   for (int i = 0; i < v1.size(); i++) {
    v.add(v1.get(i));
   }
   if (v.isEmpty()) {
    v.add(str);
   }
   return v.toArray();
  }

  @Override
  public void itemStateChanged(ItemEvent event) {
   if (event.getStateChange() == ItemEvent.SELECTED) {
    int caretPosition = editor.getCaretPosition();
    //System.out.println("c="+caretPosition);
    if (caretPosition != -1) {
     try {
      editor.moveCaretPosition(caretPosition);
     } catch (IllegalArgumentException ex) {
      ex.printStackTrace();
     }
    }
   }
  }

 }
