</
  define p: output$=24;
  define q: input$=1;
  define r: output$=23;
  
  alw(!(p and !q ) or (alw(!q);next (r and !q)))
/>