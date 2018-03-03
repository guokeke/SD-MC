</
  define p: output$=23;
  define q: input$=4;
  define r: output$=25;
  
  alw(!(p and !q ) or (alw(!q);next (r and !q)))
/>