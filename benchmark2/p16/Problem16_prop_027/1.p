</
  define p: input$=2 ;
  define q: output$=24;
  define r: output$=25;
  
  alw(!(p and !q ) or (alw(!q);next (r and !q)))
/>