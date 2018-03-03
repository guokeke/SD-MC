</
  define p: input$=5;
  define q: output$=25;
  define r: output$=24;
  
  alw(!(p and !q ) or (alw(!q);next (r and !q)))
/>
