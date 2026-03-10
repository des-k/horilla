class TimeFormattingUtility {
    constructor() {
        // Default time format
        this.timeFormat = 'hh:mm A'; // Default to 12-hour format
    }

    setTimeFormat(format) {
        // Save the selected format to localStorage
        localStorage.setItem('selectedTimeFormat', format);
        this.timeFormat = format;
    }

    getFormattedTime(time) {
        const rawTime = (time || '').toString().trim().replace(/,+$/, '');
        const placeholderValues = new Set(['', '-', 'None', 'none', 'null', 'Invalid date']);
        if (placeholderValues.has(rawTime)) {
            return '-';
        }

        if (!localStorage.getItem('selectedTimeFormat')) {
            function fetchData(callback) {
                $.ajax({
                    url: '/settings/get-time-format/',
                    method: 'GET',
                    data: { csrfmiddlewaretoken: getCookie('csrftoken') },
                    success: function(response) {
                        var time_format = response.selected_format;
                        callback(time_format);
                    },
                });
            }

            fetchData(function(time_format) {
                if (time_format) {
                    localStorage.setItem('selectedTimeFormat', time_format);
                } else {
                    localStorage.setItem('selectedTimeFormat', 'hh:mm A');
                }
            });
        }

        const storedTimeFormat = (localStorage.getItem('selectedTimeFormat') || 'hh:mm A')
            .replace(/:ss/g, '')
            .replace(/ss/g, '');

        const parsed = moment(rawTime, [
            'HH:mm:ss',
            'HH:mm',
            'H:mm:ss',
            'H:mm',
            'hh:mm A',
            'h:mm A',
            'hh:mm:ss A',
            'h:mm:ss A',
        ], true);

        if (!parsed.isValid()) {
            const compactMatch = rawTime.match(/^(\d{1,2}:\d{2})(?::\d{2})?$/);
            return compactMatch ? compactMatch[1] : rawTime;
        }

        return parsed.format(storedTimeFormat);
    }

    // Additional method for getting formatted time in 12-hour format
    getFormattedTime12Hour(time) {
        return this.getFormattedTime(time).replace(/^(\d{1,2}:\d{2}):\d{2}$/, '$1');
    }
}

// Create an instance of the TimeFormattingUtility
const timeFormatter = new TimeFormattingUtility();

// Retrieve the selected time format from localStorage
const storedTimeFormat = localStorage.getItem('selectedTimeFormat');

if (storedTimeFormat) {
    // If a time format is stored, set it in the utility
    timeFormatter.setTimeFormat(storedTimeFormat);
}
