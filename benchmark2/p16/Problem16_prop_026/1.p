</
  define p: output$=26;
  define q: input$=1;
  define r: output$=25;
  
  alw(!(p and !q ) or (alw(!q);next (r and !q)))
/>
