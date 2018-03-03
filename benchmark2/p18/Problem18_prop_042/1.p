</
  define p: input$=1;
  define q: input$=5;
  define r: output$=21;
  
  alw(!(p and !q ) or (alw(!q);next (r and !q)))
/>