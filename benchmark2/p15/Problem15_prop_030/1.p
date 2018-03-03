</
  define p: input$=4;
  define q: output$=21;
  define r: output$=25;
  
  alw(!(p and !q ) or (alw(!q);next (r and !q)))
/>