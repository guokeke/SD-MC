</
  define p: input$=3;
  define q: input$=6;
  define r: output$=21;
  
  alw(!(p and !q ) or (alw(!q);next (r and !q)))
/>
