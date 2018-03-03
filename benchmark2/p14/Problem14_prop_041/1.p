</
  define p: input$=5;
  define q: input$=4;
  define r: output$=26;
  
  alw(!(p and !q ) or (alw(!q);next (r and !q)))
/>