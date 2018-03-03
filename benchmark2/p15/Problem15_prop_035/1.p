</
  define p: input$=4;
  define q: input$=6;
  define r: output$=23;
  
  alw(!(p and !q ) or (alw(!q);next (r and !q)))
/>