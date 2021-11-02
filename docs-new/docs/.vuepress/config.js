module.exports = {
    title: 'CPChian Docs',
    description: 'Just playing around',
    themeConfig: {
        nav: [
          { text: 'Guide', link: '/' },
          { text: 'API', link: '/api/rpc' },
          { text: 'Github', link: 'https://github.com/' },
        ],
        sidebar: [
          {
            title: 'QUICK START',
            collapsable: false,
            children: [
                '/quickstart/quickstart-beginner',
                '/quickstart/quickstart'
            ]
          },
          {
            title: 'PRELIMINARIES',
            collapsable: false,
            children: [
              '/preliminaries/abstract',
              '/preliminaries/basic_information',
              '/preliminaries/configuration',
              '/preliminaries/installation',
              '/preliminaries/overview'
            ]
          },
          {
            title: 'API',
            collapsable: false,
            children: [
              '/api/rpc',
              '/api/cpc_fusion'
            ]
          },
          {
            title: 'DETAILED ALGORITHMS',
            collapsable: false,
            children: [
              '/detailed_algorithms/consensus',
              '/detailed_algorithms/election',
              '/detailed_algorithms/implementation'
            ]
          },
          {
            title: 'SMART CONTRACTS',
            collapsable: false,
            children: [
              '/smart_contracts/built_in_sm',
              '/smart_contracts/reward_sm'
            ]
          },
          {
            title: 'TEST',
            collapsable: false,
            children: [
              '/test/test-overview',
              '/test/testcase'
            ]
          },
          {
            title: 'PERFORMANCE',
            collapsable: false,
            children: [
              '/performance/performance'
            ]
          },
          {
            title: 'MISC',
            collapsable: false,
            children: [
              '/misc/faq',
              '/misc/glossary',
              '/misc/mapping',
            ]
          },
        ],
        sidebarDepth: 2
      },
      markdown: {
        toc: {
          includeLevel:[1, 2, 3, 4]
        }
      },
      configureWebpack: {
        resolve: {
          alias: {
            // '@alias': 'path/to/some/dir'
          }
        }
      }
  }
