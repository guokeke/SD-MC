</
  define p: output$=24;
  define q: input$=2;
  define r: output$=21;
  
  alw(!(p and !q ) or (alw(!q);next (r and !q)))
/>